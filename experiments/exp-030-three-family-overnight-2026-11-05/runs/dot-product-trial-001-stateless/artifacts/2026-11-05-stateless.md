# Bounded agent run

```text
artifact_id: 2026-11-05-stateless
experiment_id: dot-product-trial-001-stateless
condition: stateless
task_id: multi-agent-dot-product-roundtrip-pilot
model: gpt-6.1-sol
reasoning_effort: medium
starting_commit: b5df08f54d45608c2aad01a58ac3dee5ff95d8f6
artifact_snapshot: {'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/source.pdf': '620f7b063a68cb4d64cb964fee589815266ae11b934a03a864a59e05a48167eb', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/PROMPT.txt': 'f2997ebd93f8f4b45ad103ee0a408f36c6f2ad20a7927b13234c2d1a5e10fb84', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/source.txt': '3d8a7e83fadefa36f92fc47d31c4937e3edda6734b08002fa026ffc68d93abef', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/support/Research/Projects/BinaryTreeReduction/Tree.lean': '336f0a53173d33a3630bb98428faafab87ebc0dbe606eead4f9eb2cbd95cd480', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/support/Research/Projects/BinaryTreeReduction/Reduction.lean': '7bb500f0306604e5c07f7621ff0603ffa172ed8944374abd9d269896b8ab26b5', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/support/Research/Projects/BinaryTreeReduction/Algorithm.lean': 'b2736b0297959943cf2913729c2111de051ff1a95f1d5cd4e930a09249e000a1', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/support/Research/Common/FloatingPoint/Gamma.lean': '146665586383021bfd9635f035823ee12513685241abf366ab61921f1febf843', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/inputs/support/Research/Common/FloatingPoint/Model.lean': 'b3730c493db6864297bc3ce04f2be01c9811a26d211dc268f10a50bf3894eece', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/memory/general-lean.md': 'cce6d9aa5a0ac2fc04e8f249914b7306946a6cc88994bb8bda0f50c38232039d', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/memory/index.md': '38f57977b6c743170ae683ba5f733cec02d2b17da037a70d33ace11249bcc3c5', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/evaluator/Research.lean': 'cde6db415a0bb4f48616881e996c74d28d73620487ff087b0c29fb9aad893697', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/evaluator/requirements.json': '2ecce2638547aea9f75dbad3c816aae39c2fe386e05236bb51bf6de80181098e', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/evaluator/verify.sh': 'dc05e34574ee64fdd628f5a14fd3b5d5fbbe09d499f82eb3ce73181ff7d15ef6', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/evaluator/lean-toolchain': 'db7bb24b756d745bbde83fe92718b51bd3625dae3701ba0f598d0eedcd3f3028', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/evaluator/lakefile.toml': 'f7a30d07baaa36a9569f8abb86d35e55c74e7f8075a3d33a203217f5efc9a909', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/evaluator/REVIEWER.txt': '800d9daf958e7984a684dcbe9d8b4f4a098c0b353a60ec8676a4b6cd213c5852', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/evaluator/lake-manifest.json': '504c0a3c7e4f543bd5786d646e64d3549e5e8e8a226f0edca597bc684d5b5939', 'experiments/exp-030-three-family-overnight-2026-11-05/runs/dot-product-trial-001-stateless/experiment.json': 'b2f3f1c6f32d8347b55f2c2bf1ddfd4408efa16cb88f033161e7dcac9bd25fe2', 'pipeline/resources.py': '1cf72ddc6cedefbe93d7d41199e355e163a95c69d8368570cdd5b5c32eef41c9', 'pipeline/run.py': '79721e0e4ec5a130af02d55b93a02d8897947566a28668afa1bba903ccbc2043', 'pipeline/worker.py': 'a8152114fc2e9ea38d9e2a856220fb480d4cc6f7090aef75918ad7ad51765f6a', 'pipeline/smoke_model.py': '3dabe73c64b0b4c13fc04a31d9a82d4f4cad4452d2583c69869be70f72a9ae53', 'pipeline/engine.py': '0ebb6552c762f39fd02aca10f02396dc0cf60c9d761c26a9b5b6e5dd3871d9b9', 'pipeline/critic_benchmark.py': '4f05b57d833bd276a26f193570b88fe2eba0f6931f4b911f531526514714d3a8', 'pipeline/verify.py': 'a885c2c7c297d10497410e7389bace1e53255b7bee3cee2f686d5c9c39c22f8d', 'pipeline/stages.py': 'e82b52a781b2ccf2b0d1e38f9cf971d7de86c69a5a3a039b1635d16c64d4808a', 'pipeline/verify.sh': 'dc05e34574ee64fdd628f5a14fd3b5d5fbbe09d499f82eb3ce73181ff7d15ef6', 'pipeline/roundtrip.py': 'a9defc7bd028b66d90ba1d8da6414cd0805c215a7f45c7b8e7abf44054f0b2fa', 'pipeline/artifacts.py': '1810bfca20ddbceecf9995021e099492eb2d7abd092ef1d063f03e903282fd82', 'pipeline/roles.py': '92445f90205da7fd1ea136ff571575cb8a5cea826161aa5f23faa30e251f2528', 'pipeline/formal_context.py': '556fe4202db760b924ca89045e23d6f5dfd1dfe9b33110648ddc369ec54fb057', 'pipeline/batch.py': 'd63bb3df1831fa82d35265fe830c9ae735c45eb81c3619d7130fda25aea70a56', 'pipeline/agent.py': '3645e7d35478b2b8558d45ebe4e906e073bab41b24d778cef8076114bc7a8597', 'pipeline/role_agent.py': '3fe71ebd480677b341ac2a605cb1b0239fe7a33b7c2a9971f0ff9dc5703d6811', 'pipeline/critic.py': '21d211337c58d3a8d0ec872120454c8360f1b6f0ae25d40b24d4486c6be65acf', 'pipeline/ExtractContext.lean': 'bb1dd9980d3d02547eee7594a905a2bc8dea8a15d93f1c2eb6c4ab17f465c047', 'pipeline/passes.py': 'a2eedc54d5d42b3ccb9bb12beffeab5317a6c69de98f0be0877b4a393ffb4263', 'pipeline/docker/Dockerfile': '9f9c499509672ebbfeb1817521c175861dd3eb722d85d0ab1da884e604e991d1', 'pipeline/docker/Dockerfile.ready': '8fba11b7730c46a8b41dfdc98c9c56efdff4c1a28227e1a00d3eb96369fdc8ba', 'pipeline/docker/proxy.py': '2e79cf96635643f540385207755ad37c3c4265795929cbb63ae2e85e9b63e72b'}
retrieved_artifacts: []
verification_command: bash pipeline/verify.sh
success: True
status: verified
memory_mode: stateless
```

## Request

Compare equal fixed pass budgets, with and without frozen artifacts.

## Target

multi-agent-dot-product-roundtrip-pilot

## Result

accepted

## Decisions and reasoning

Only verifier/critic evidence authorizes acceptance. Uncertain or invalid reviews stop for attention.

## What worked

See pass-level evidence; no benefit inferred automatically.

## What failed

See recorded failed gates and diagnostics; infrastructure failures are separate.

## Reusable observations

Not promoted. Any candidate lesson needs review and answer-leakage checks.

## Evidence

[Structured run record](2026-11-05-stateless.json)

## Remaining limitations

External-memory reuse only; no weight learning or causal conclusion. Human semantic sign-off not claimed.

## Metrics

Unknown measurements remain unknown; see the JSON record.

