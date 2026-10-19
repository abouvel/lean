"""Shared container machinery. Mathematical inputs and settings come from config."""
import json
from pathlib import Path
import shutil
import subprocess

TOOLS = Path(__file__).resolve().parent
CONFIG_FILES = ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "Research.lean")


def call(args, **kwargs):
    return subprocess.run([str(a) for a in args], check=kwargs.pop("check", True),
                          capture_output=True, text=True, **kwargs)


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value if isinstance(value, str) else json.dumps(value, indent=2) + "\n")


def ownership(path):
    # Disposable actor workspaces only; never call on inputs or the repository.
    for file in (path, *path.rglob("*")):
        if file.is_symlink():
            raise RuntimeError(f"Unexpected workspace symlink: {file}")
        file.chmod(0o777 if file.is_dir() else 0o666)


def mount(source, target, readonly=False):
    return ["--mount", f"type=bind,source={source},target={target}" + (",readonly" if readonly else "")]


class Engine:
    def __init__(self, directory, config, lean, packages, auth, guard):
        self.directory, self.config = directory, config
        self.lean, self.packages, self.auth = lean, packages, auth
        self.guard = guard
        self.conditions = tuple(config["conditions"])
        self.image = config["image"]
        self.net = f"research-{directory.name}-internal"
        self.proxy = f"research-{directory.name}-proxy"

    def network(self):
        if call(["docker", "network", "inspect", self.net], check=False).returncode:
            call(["docker", "network", "create", "--internal", self.net])
        existing = call(["docker", "inspect", self.proxy], check=False)
        if not existing.returncode:
            if json.loads(existing.stdout)[0]["State"]["Running"]:
                return
            raise RuntimeError("A stopped task proxy exists; inspect it before proceeding.")
        call(["docker", "run", "-d", "--name", self.proxy, "--read-only", "--cap-drop=ALL",
              "--security-opt=no-new-privileges", "--pids-limit=64", "--memory=256m",
              "--network", "bridge", *mount(TOOLS / "docker/proxy.py", "/proxy.py", True),
              self.image, "python3", "/proxy.py"])
        call(["docker", "network", "connect", "--alias", "model-proxy", self.net, self.proxy])

    def container(self, condition, *, workspace=None, output=None, spec=None, offline=False, reviewer=False):
        work = workspace or self.directory / condition / "workspace"
        out = output or self.directory / condition / "output"
        resources = self.config["resources"]
        args = ["docker", "run", "--rm", "--read-only", "--cap-drop=ALL",
                "--security-opt=no-new-privileges", f"--pids-limit={resources['pids']}",
                f"--memory={resources['memory']}", f"--cpus={resources['cpus']}",
                "--tmpfs", "/tmp:rw,nosuid,nodev,size=2g,mode=1777",
                "--tmpfs", "/home/researcher:rw,nosuid,nodev,size=256m,uid=1100,gid=1100,mode=0700",
                "--network", "none" if offline else self.net,
                *mount(work, "/workspace", reviewer), *mount(out, "/output"),
                *mount(self.lean, "/opt/lean", True),
                *mount(self.packages, "/workspace/.lake/packages", True),
                *mount(spec or self.directory / self.config["inputs"], "/spec", True),
                *mount(TOOLS / "agent.py", "/runner/entry.py", True)]
        dependencies = sorted(p.name for p in self.packages.iterdir() if p.is_dir())
        args += ["-e", f"GIT_CONFIG_COUNT={len(dependencies)}"]
        for i, dependency in enumerate(dependencies):
            args += ["-e", f"GIT_CONFIG_KEY_{i}=safe.directory", "-e",
                     f"GIT_CONFIG_VALUE_{i}=/workspace/.lake/packages/{dependency}"]
        for name in CONFIG_FILES:
            args += mount(work / name, "/workspace/" + name, True)
        if not offline:
            args += mount(self.auth, "/auth/auth.json", True)
            for key in ("HTTPS_PROXY", "HTTP_PROXY", "ALL_PROXY"):
                args += ["-e", key + "=http://model-proxy:3128"]
            args += ["-e", "NO_PROXY=localhost,127.0.0.1"]
        if condition == "retrieved" and not reviewer and not offline:
            args += mount(self.directory / self.config["memory"], "/memory", True)
        limit = self.config["critic_seconds" if reviewer else "builder_seconds"]
        args += ["-e", "EXPERIMENT_MODEL=" + self.config["model"],
                 "-e", "REASONING_EFFORT=" + self.config["reasoning_effort"],
                 "-e", "MEMORY_MODE=" + condition,
                 "-e", "RUN_KIND=" + ("reviewer" if reviewer else "builder"),
                 "-e", f"TIME_LIMIT_SECONDS={limit}"]
        return args

    def preflight(self):
        self.guard()
        self.network()
        test = '''import json, os, pathlib, socket, subprocess
p=pathlib.Path
r={"host_repository_absent":not p(HOST_REPOSITORY).exists(),
   "docker_socket_absent":not p("/var/run/docker.sock").exists(),
   "no_project_git":not p("/workspace/.git").exists(),
   "no_previous_solution":not p("/workspace/Research/Projects").exists(),
   "no_worked_examples":not p("/workspace/Research/Examples.lean").exists(),
   "reviewer_and_hidden_tests_absent":not p("/spec/REVIEWER.txt").exists(),
   "memory_visibility_correct":p("/memory/index.md").exists()==(os.environ["MEMORY_MODE"]=="retrieved")}
try:
 p("/spec/should-not-write").write_text("x");r["spec_read_only"]=False
except OSError:r["spec_read_only"]=True
try:
 s=socket.create_connection(("1.1.1.1",443),timeout=3);s.close();r["direct_egress_blocked"]=False
except OSError:r["direct_egress_blocked"]=True
v=subprocess.run(["curl","-I","--max-time","8","https://github.com"],capture_output=True,text=True)
r["github_blocked"]=v.returncode!=0 and "403" in v.stdout+v.stderr
v=subprocess.run(["lean","--version"],capture_output=True,text=True)
r["lean_version_correct"]=v.returncode==0 and "4.28.0" in v.stdout
v=subprocess.run(["codex","--version"],capture_output=True,text=True)
r["codex_version_correct"]=v.returncode==0 and "0.162.0" in v.stdout
print(json.dumps(r));raise SystemExit(0 if all(r.values()) else 1)
'''
        test = "HOST_REPOSITORY = " + repr(str(TOOLS.parent)) + "\n" + test
        reports = {}
        for condition in self.conditions:
            result = call([*self.container(condition), self.image, "python3", "-c", test], check=False, timeout=45)
            reports[condition] = {"exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
        work, out = self.directory / "preflight/workspace", self.directory / "preflight/output"
        shutil.copytree(self.directory / "stateless/workspace", work)
        out.mkdir(parents=True)
        ownership(work)
        ownership(out)
        result = call([*self.container("stateless", workspace=work, output=out, offline=True),
                       self.image, "lake", "build"], check=False, timeout=120)
        reports["lean_smoke_build"] = {"exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
        save(self.directory / "preflight.json", reports)
        if any(item["exit_code"] != 0 for item in reports.values()):
            raise RuntimeError("Preflight failed; no proof builder launched.")

    def connectivity(self):
        self.guard()
        self.network()
        output = self.directory / "connectivity"
        output.mkdir()
        ownership(output)
        result = call([*self.container("stateless", output=output),
                       *mount(TOOLS / "smoke_model.py", "/runner/smoke_model.py", True),
                       self.image, "python3", "/runner/smoke_model.py"], check=False, timeout=110)
        save(output / "container.log", result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError("Connectivity check failed; no proof builder launched.")

    def builders(self):
        self.guard()
        self.network()
        for condition in self.conditions:
            output = self.directory / condition / "output"
            if (output / "events.jsonl").exists():
                raise RuntimeError(f"Existing builder output: {condition}")
            print("BUILD", condition, flush=True)
            with (self.directory / condition / "container.log").open("w") as log:
                result = subprocess.run([*self.container(condition), self.image, "python3", "/runner/entry.py"],
                                        stdout=log, stderr=subprocess.STDOUT,
                                        timeout=self.config["builder_seconds"] + 60)
            save(output / "container-exit.json", {"exit_code": result.returncode})

    def evaluate(self):
        self.guard()
        trusted = self.directory / self.config["evaluator"]
        for condition in self.conditions:
            dest = self.directory / condition / "evaluation-workspace"
            if dest.exists():
                raise RuntimeError("Evaluation exists; preserve the previous result.")
            (dest / "Research").mkdir(parents=True)
            (dest / ".lake").mkdir()
            for name in CONFIG_FILES[:-1]:
                shutil.copyfile(trusted / name, dest / name)
            actor = self.directory / condition / "workspace/Research"
            for file in actor.rglob("*.lean"):
                if file.is_symlink() or any(p.is_symlink() for p in file.parents if p != actor.parent):
                    raise RuntimeError("Submission symlink rejected")
                target = dest / "Research" / file.relative_to(actor)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(file, target)
            modules = ["Research." + ".".join(p.relative_to(dest / "Research").with_suffix("").parts)
                       for p in sorted((dest / "Research").rglob("*.lean"))]
            save(dest / "Research.lean", "\n".join("import " + module for module in modules) + "\n")
            output = self.directory / condition / "evaluation"
            output.mkdir()
            ownership(dest)
            ownership(output)
            result = call([*self.container(condition, workspace=dest, output=output, offline=True),
                           *mount(trusted / "verify.sh", "/trusted/verify.sh", True),
                           *mount(TOOLS / "verify.py", "/trusted/verify_candidate.py", True),
                           self.image, "python3", "/trusted/verify_candidate.py"], check=False, timeout=270)
            save(output / "container.log", result.stdout + result.stderr)
            save(output / "container-exit.json", {"exit_code": result.returncode})

    def review(self):
        self.guard()
        self.network()
        for condition in self.conditions:
            spec = self.directory / condition / "reviewer-spec"
            spec.mkdir()
            for name in ("source.txt", "source.pdf"):
                shutil.copyfile(self.directory / self.config["inputs"] / name, spec / name)
            shutil.copyfile(self.directory / self.config["evaluator"] / "REVIEWER.txt", spec / "REVIEWER.txt")
            output = self.directory / condition / "review"
            output.mkdir()
            ownership(output)
            with (output / "container.log").open("w") as log:
                result = subprocess.run([*self.container(condition,
                    workspace=self.directory / condition / "evaluation-workspace", output=output,
                    spec=spec, reviewer=True),
                    *mount(self.directory / condition / "evaluation", "/evaluation", True),
                    self.image, "python3", "/runner/entry.py"], stdout=log, stderr=subprocess.STDOUT,
                    timeout=self.config["critic_seconds"] + 60)
            save(output / "container-exit.json", {"exit_code": result.returncode})

    def summarize(self):
        summary = {"experiment_id": self.directory.name, "conditions": {},
                   "limitations": self.config.get("limitations", [])}
        for condition in self.conditions:
            item = {}
            for label, name in (("actor", "output/metrics.json"), ("verification", "evaluation/verification.json"),
                                ("critic", "review/review.json")):
                path = self.directory / condition / name
                try:
                    item[label] = json.loads(path.read_text()) if path.exists() else "unavailable"
                except json.JSONDecodeError:
                    item[label] = "invalid JSON; inspect original report"
            summary["conditions"][condition] = item
        save(self.directory / "comparison.json", summary)
        return summary

    def cleanup(self):
        # Exact task-owned Docker names only; never delete experiment files.
        logs = call(["docker", "logs", self.proxy], check=False)
        save(self.directory / "network-proxy.log", logs.stdout + logs.stderr)
        call(["docker", "stop", self.proxy], check=False)
        call(["docker", "rm", self.proxy], check=False)
        call(["docker", "network", "rm", self.net], check=False)
