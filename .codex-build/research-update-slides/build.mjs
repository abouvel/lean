import fs from "node:fs/promises";
import path from "node:path";
import { createRequire } from "node:module";
import { pathToFileURL } from "node:url";

const require = createRequire(import.meta.url);
const moduleRoot = "C:/Users/austi/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules";
process.env.RUNTIME_NODE_MODULES = moduleRoot;
process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES = moduleRoot;
const artifactEntry = require.resolve("@oai/artifact-tool", { paths: [moduleRoot] });
const { Presentation, PresentationFile } = await import(pathToFileURL(artifactEntry).href);

const workspaceDir = "//wsl.localhost/Ubuntu/home/abouvel/fall26/research";
const buildDir = path.join(workspaceDir, ".codex-build", "research-update-slides-v4");
const draftPath = path.join(buildDir, "research-update-draft.pptx");
const finalPath = path.join(workspaceDir, "output", "slides", "binary-tree-agent-memory-update-v4.pptx");
const validationWorkspace = "C:/Users/austi/Documents/Codex/.codex-build/research-update-slides";
const validationDraftPath = path.join(validationWorkspace, "stage", `research-update-draft-${Date.now()}.pptx`);
const validationFinalPath = path.join(validationWorkspace, "output", `binary-tree-agent-memory-update-${Date.now()}.pptx`);
const validationReceiptPath = path.join(validationWorkspace, "private", `validation-${Date.now()}.json`);
const skillDir = "C:/Users/austi/.codex/plugins/cache/openai-primary-runtime/presentations/26.1011.11113/skills/presentations";
const pythonExecutable = "C:/Users/austi/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe";

const W = 1280;
const H = 720;
const FONT = "Aptos";
const C = {
  navy: "#0B1739",
  blue: "#2563EB",
  cyan: "#06B6D4",
  green: "#16A34A",
  amber: "#D97706",
  red: "#DC2626",
  ink: "#172033",
  gray: "#64748B",
  pale: "#E8EEF8",
  line: "#CBD5E1",
  white: "#FFFFFF",
  bg: "#F7F9FC",
};

function addText(slide, text, x, y, width, height, opts = {}) {
  const box = slide.shapes.add({
    geometry: "textbox",
    position: { left: x, top: y, width, height },
    fill: "none",
    line: { style: "solid", fill: "none", width: 0 },
  });
  box.text = text;
  box.text.style = {
    fontFamily: FONT,
    fontSize: opts.fontSize ?? 20,
    bold: opts.bold ?? false,
    color: opts.color ?? C.ink,
    alignment: opts.alignment ?? "left",
    verticalAlignment: opts.verticalAlignment ?? "middle",
  };
  return box;
}

function addBox(slide, x, y, width, height, opts = {}) {
  return slide.shapes.add({
    geometry: opts.geometry ?? "roundRect",
    position: { left: x, top: y, width, height },
    fill: opts.fill ?? C.white,
    line: {
      style: "solid",
      fill: opts.line ?? C.line,
      width: opts.lineWidth ?? 1,
    },
    borderRadius: opts.geometry ? undefined : "rounded-lg",
  });
}

function addLine(slide, x1, y1, x2, y2, color = C.line, width = 2) {
  const left = Math.min(x1, x2);
  const top = Math.min(y1, y2);
  const horizontalFlip = x2 < x1;
  const verticalFlip = y2 < y1;
  return slide.shapes.add({
    geometry: "line",
    position: {
      left,
      top,
      width: Math.abs(x2 - x1),
      height: Math.abs(y2 - y1),
      horizontalFlip,
      verticalFlip,
    },
    fill: "none",
    line: { style: "solid", fill: color, width },
  });
}

function addHeader(slide, title, number) {
  addText(slide, `0${number}`, 70, 38, 44, 26, { fontSize: 13, bold: true, color: C.blue });
  addText(slide, title, 70, 72, 1100, 58, { fontSize: 32, bold: true, color: C.navy });
  addLine(slide, 70, 140, 1210, 140, C.line, 1);
}

function addFooter(slide, text) {
  addText(slide, text, 70, 675, 1140, 22, { fontSize: 11, color: C.gray, alignment: "right" });
}

function addNode(slide, label, cx, cy, opts = {}) {
  const r = opts.r ?? 28;
  addBox(slide, cx - r, cy - r, r * 2, r * 2, {
    geometry: "ellipse",
    fill: opts.fill ?? C.white,
    line: opts.line ?? C.blue,
    lineWidth: opts.lineWidth ?? 2,
  });
  addText(slide, label, cx - r, cy - r, r * 2, r * 2, {
    fontSize: opts.fontSize ?? 16,
    bold: true,
    alignment: "center",
  });
}

const presentation = Presentation.create({ slideSize: { width: W, height: H } });

// Slide 1: the algorithm and five-input test.
{
  const slide = presentation.slides.add();
  slide.background.fill = C.bg;
  addHeader(slide, "Binary-tree floating-point reduction", 1);
  addText(slide,
    "Completed: Algorithm 1 for every nonempty list, with a deterministic backward-error theorem in Lean.",
    70, 153, 1120, 48, { fontSize: 20, color: C.gray });

  const xs = [170, 350, 530, 710, 890];
  const labels = ["2", "3", "4", "5", "6"];
  for (let i = 0; i < xs.length; i++) addNode(slide, labels[i], xs[i], 260);
  addText(slide, "LEVEL 0", 70, 245, 70, 28, { fontSize: 12, bold: true, color: C.gray });

  const l1 = [260, 620, 890];
  addLine(slide, xs[0], 289, l1[0], 337, C.blue, 2);
  addLine(slide, xs[3], 289, l1[0], 337, C.blue, 2);
  addLine(slide, xs[1], 289, l1[1], 337, C.blue, 2);
  addLine(slide, xs[4], 289, l1[1], 337, C.blue, 2);
  addLine(slide, xs[2], 289, l1[2], 337, C.amber, 2);
  addNode(slide, "7", l1[0], 370, { fill: "#DBEAFE" });
  addNode(slide, "9", l1[1], 370, { fill: "#DBEAFE" });
  addNode(slide, "4", l1[2], 370, { fill: "#FEF3C7", line: C.amber });
  addText(slide, "LEVEL 1", 70, 355, 70, 28, { fontSize: 12, bold: true, color: C.gray });
  addText(slide, "carried", 930, 356, 85, 24, { fontSize: 12, bold: true, color: C.amber });

  const l2 = [440, 710];
  addLine(slide, l1[0], 399, l2[0], 447, C.blue, 2);
  addLine(slide, l1[2], 399, l2[0], 447, C.blue, 2);
  addLine(slide, l1[1], 399, l2[1], 447, C.amber, 2);
  addNode(slide, "11", l2[0], 480, { fill: "#DBEAFE" });
  addNode(slide, "9", l2[1], 480, { fill: "#FEF3C7", line: C.amber });
  addText(slide, "LEVEL 2", 70, 465, 70, 28, { fontSize: 12, bold: true, color: C.gray });

  addLine(slide, l2[0], 509, 575, 557, C.blue, 2);
  addLine(slide, l2[1], 509, 575, 557, C.blue, 2);
  addNode(slide, "20", 575, 590, { r: 32, fill: "#DCFCE7", line: C.green, lineWidth: 3 });
  addText(slide, "LEVEL 3", 70, 575, 70, 28, { fontSize: 12, bold: true, color: C.gray });

  addText(slide, "General guarantee", 1020, 245, 190, 40, { fontSize: 22, bold: true, color: C.navy });
  addText(slide, "Every input occurrence survives\n\nCarries add no rounding operation\n\nL = ⌈log₂ n⌉\nDepth ≤ L",
    1020, 298, 190, 230, { fontSize: 20, verticalAlignment: "top" });
  addText(slide, "ŷ = Σᵢ (xᵢ + Δxᵢ)     |Δxᵢ| ≤ γ_L |xᵢ|     γ_L = Lu / (1 − Lu)",
    180, 636, 1000, 32, {fontSize: 23, bold: true, color: C.navy, alignment: "center"});
  addFooter(slide, "Abstract relative-error model, Lu < 1. IEEE 754 bit semantics and probabilistic bounds remain outside this result.");
  slide.speakerNotes.text = `Each row has fewer partial sums until one result remains. The five-input example checks the paper's exact pairing. A carried value gets no extra addition or rounding.

Lean proves this for every nonempty list: every input survives, including duplicates, and depth is at most ceil(log2 n). Under the relative-error assumption, the computed answer is the exact sum of slightly perturbed inputs, bounded by gamma.

If asked: the dot product adds one multiplication error per leaf. The current result is deterministic and uses an abstract model, without IEEE 754 bit semantics.

Code: Research/Projects/BinaryTreeReduction/{Algorithm,Examples,Reduction,DotProduct}.lean; Research/Common/FloatingPoint/Model.lean`;
}

// Slide 2: proof architecture and verified result.
{
  const slide = presentation.slides.add();
  slide.background.fill = C.white;
  addHeader(slide, "Proof pipeline and instruction fidelity", 2);
  addText(slide, "The agent proposes Lean code. Formal checking and semantic review provide separate acceptance gates.",
    70, 153, 1120, 48, {fontSize:20,color:C.gray});

  const xs = [70, 365, 660, 955];
  const titles = ["Specify", "Construct", "Check", "Record"];
  const descriptions = ["Paper assumptions\nLean statement", "Small lemmas\nCompile and repair", "Full build + scans\nSemantic review", "Prompts and decisions\nVerified lessons"];
  for (let i=0;i<4;i++) {
    if(i<3) addLine(slide,xs[i]+245,288,xs[i+1],288,C.line,3);
    addBox(slide,xs[i],230,245,120,{fill:i===2?"#DCFCE7":C.bg,line:i===2?C.green:C.line});
    addText(slide,titles[i],xs[i]+16,240,213,34,{fontSize:24,bold:true,color:C.navy});
    addText(slide,descriptions[i],xs[i]+16,283,213,55,{fontSize:19});
  }
  addText(slide,"My interventions",70,388,300,36,{fontSize:24,bold:true,color:C.navy});
  addText(slide,"Review assumptions and the target statement\nSet exact tests and decompose the argument\nReview the result against the source theorem",
    70,435,560,145,{fontSize:22,verticalAlignment:"top"});
  addText(slide,"Observable evidence",680,388,450,36,{fontSize:24,bold:true,color:C.navy});
  addText(slide,"Exact levels and unchanged carry structure\nGeneral preservation and depth theorems\nBuild result, scans, and decision records",
    680,435,530,145,{fontSize:22,verticalAlignment:"top"});
  addText(slide,"Full project build passed. No proof placeholders or project-defined axioms. Aristotle calls: 0.",
    70,605,1140,48,{fontSize:20,bold:true,color:C.green});
  addFooter(slide,"Aristotle remains an optional fallback for an isolated blocked lemma after local decomposition.");
  slide.speakerNotes.text = `I guided the specification, tests, and decomposition. The coding agent generated and repaired substantial parts of the Lean code. Lean checked the resulting proofs.

The core argument is induction: bound the two subtrees, then account for one more rounding factor. I also review the statement against the paper, because Lean can verify a correctly proved but incorrectly specified theorem.

We used no Aristotle for this run. The 8,036 figure counts build jobs, including dependencies, rather than independent tests. The final gate builds the project and scans for sorry, admit, and custom axiom declarations.

Evidence: pipeline/verify.sh; projects/binary-tree-reduction/theorem.md; artifacts/runs/2026-10-11-algorithm1-offset-reduction.md`;
}

// Slide 3: memory-ablation research plan.
{
  const slide = presentation.slides.add();
  slide.background.fill = C.bg;
  addHeader(slide, "Proposed experiment: learning from proof experience", 3);
  addText(slide,
    "Can a fixed model use verified experience to solve new floating-point proofs more reliably or at lower cost?",
    70, 153, 1120, 48, { fontSize: 20, color: C.gray });

  addText(slide, "Fixed model, reasoning setting, tools, budgets, starting code, and verification", 125, 218, 1030, 36,
    { fontSize: 18, bold: true, color: C.navy, alignment: "center" });

  addBox(slide, 90, 285, 460, 220, { fill: C.white, line: C.line, lineWidth: 2 });
  addText(slide, "Stateless condition", 125, 310, 390, 42, { fontSize: 24, bold: true, color: C.navy });
  addText(slide, "Fresh context with no research memory\n\nShared Lean prerequisites and Mathlib\n\nUnfinished target and acceptance tests",
    125, 365, 390, 125, { fontSize: 19, color: C.ink, verticalAlignment: "top" });

  addBox(slide, 730, 285, 460, 220, { fill: "#EFF6FF", line: C.blue, lineWidth: 2 });
  addText(slide, "Artifact-enabled condition", 765, 310, 390, 42, { fontSize: 24, bold: true, color: C.blue });
  addText(slide, "Same setup plus frozen verified memory\n\nLog retrieval and decisions it changes\n\nExclude the completed target proof",
    765, 365, 390, 125, { fontSize: 19, color: C.ink, verticalAlignment: "top" });

  addLine(slide, 550, 410, 730, 410, C.line, 3);
  addText(slide, "compare", 595, 382, 90, 28, { fontSize: 14, bold: true, color: C.gray, alignment: "center" });

  addText(slide, "Measure", 90, 535, 150, 30, { fontSize: 19, bold: true, color: C.gray });
  addText(slide, "Verified proof success, time, cost, compiler attempts, Aristotle use", 250, 535, 940, 32, { fontSize: 21, bold: true, color: C.navy });
  addText(slide, "Diagnose", 90, 583, 150, 30, { fontSize: 19, bold: true, color: C.gray });
  addText(slide, "Missing lesson, missed retrieval, or incorrect application", 250, 583, 940, 32, { fontSize: 21, color: C.ink });
  addFooter(slide, "Evaluation uses held-out proofs across fresh runs. The experiment has not established improvement yet.");
  slide.speakerNotes.text = `Next, I want to compare fresh agents with and without verified memory on new proofs. Both conditions get the same starting code, model, tools, and budget. The completed target proof stays unavailable.

I will measure proof success first, then time, cost, compiler attempts, and Aristotle calls. I will also check whether the agent found and correctly applied a relevant lesson. Include the cost of creating memory.

The plasticity paper found that reuse can help, but high reuse alone does not guarantee improvement. This experiment tests external-memory adaptation with fixed model weights. We have not demonstrated a performance gain yet.

Sources: AGENTS.md; pipeline/README.md; C:/Users/austi/Downloads/2610.08902v1.pdf, sections 2-4`;
}

// Slide 4: proposed isolation boundaries and execution plan.
{
  const slide = presentation.slides.add();
  slide.background.fill = C.white;
  addHeader(slide, "Proposed isolation: one repo, separate agent containers", 4);
  addText(slide, "Each run receives only its permitted files. The agent runner and all file tools execute inside the container.",
    70,153,1140,48,{fontSize:20,color:C.gray});

  addBox(slide,375,220,530,65,{fill:C.navy,line:C.navy});
  addText(slide,"Monorepo: code, experiment specs, master artifacts",395,230,490,44,
    {fontSize:21,bold:true,color:C.white,alignment:"center"});
  addLine(slide,640,285,640,310,C.line,2);
  addLine(slide,355,310,925,310,C.line,2);
  addLine(slide,355,310,355,340,C.line,2);
  addLine(slide,925,310,925,340,C.line,2);

  addBox(slide,90,340,530,210,{fill:C.bg,line:C.line,lineWidth:2});
  addText(slide,"Stateless container",115,355,480,35,{fontSize:25,bold:true,color:C.navy});
  addText(slide,"Agent CLI + Lean 4.28.0 + Mathlib\n/workspace: identical starting code\nFresh session, no research memory",
    115,405,480,118,{fontSize:22,verticalAlignment:"top"});

  addBox(slide,660,340,530,210,{fill:"#EFF6FF",line:C.blue,lineWidth:2});
  addText(slide,"Retrieved container",685,355,480,35,{fontSize:25,bold:true,color:C.blue});
  addText(slide,"Same agent and Lean environment\n/workspace: identical starting code\n/memory: frozen snapshot, read-only",
    685,405,480,118,{fontSize:22,verticalAlignment:"top"});

  addText(slide,"Isolation rules",90,578,210,32,{fontSize:21,bold:true,color:C.navy});
  addText(slide,"Mount selected files only. Exclude answer-bearing Git history and build caches.\nRestrict network and external tools. Export logs and proofs for independent verification.",
    310,574,880,70,{fontSize:20,verticalAlignment:"top"});
  addFooter(slide,"Planned next step: build the common image, test access boundaries, then pilot the two conditions.");
  slide.speakerNotes.text = `We keep one repository, but each run gets a separate container and fresh session. The agent and all file tools execute inside it.

A host-side script copies permitted files into each workspace. It mounts the frozen artifact snapshot read-only at /memory for the retrieved condition. The stateless condition gets no memory mount.

Exclude completed proofs, answer-bearing Git history, and build outputs. Restrict other tools and network access so they cannot bypass isolation. Test those boundaries before the experiment. This setup is proposed and still needs implementation.

Reference: https://developers.openai.com/codex/cli; project protocol in AGENTS.md`;
}

// Slide 5: prioritized future research questions.
{
  const slide = presentation.slides.add();
  slide.background.fill = C.bg;
  addHeader(slide, "Future questions: beyond memory reuse", 5);
  addText(slide,"The Agent Plasticity paper finds that high reuse alone does not guarantee improvement. Gains vary by model and task.",
    70,153,1140,62,{fontSize:22,color:C.gray});

  addText(slide,"Question",70,240,490,35,{fontSize:20,bold:true,color:C.gray});
  addText(slide,"Follow-up experiment",620,240,590,35,{fontSize:20,bold:true,color:C.gray});
  addLine(slide,70,284,1210,284,C.line,1);

  const rows = [
    ["Does the agent find and apply the lesson?", "Compare normal retrieval with a relevant lesson supplied directly."],
    ["Can reflection produce better lessons?", "Use compiler failures to revise lessons. Compare with human-curated memory."],
    ["Do executable skills help more than notes?", "Compare textual advice with tested search helpers or proof procedures."],
  ];
  for(let i=0;i<rows.length;i++) {
    const y=302+i*97;
    addText(slide,rows[i][0],70,y,490,76,{fontSize:24,bold:true,color:C.navy,verticalAlignment:"top"});
    addText(slide,rows[i][1],620,y,590,76,{fontSize:22,verticalAlignment:"top"});
    if(i<rows.length-1) addLine(slide,70,y+84,1210,y+84,C.line,1);
  }
  addText(slide,"First milestone: reliable memory access and a fair baseline comparison",
    70,606,1140,40,{fontSize:23,bold:true,color:C.blue});
  addFooter(slide,"Evaluate unseen proofs and include preparation cost. Post-training remains a later question.");
  slide.speakerNotes.text = `The paper shows that retrieving and reusing memory does not explain all improvement. Relevant lessons can still be poor, too specific, or incorrectly applied. These are candidate bottlenecks, not established causal findings.

After the baseline works, I would test three changes separately: supply relevant lessons directly, improve lessons using compiler feedback, and save tested executable skills alongside notes.

Each change must improve verified performance on unseen proofs relative to its total cost. Post-training can wait until we have a reliable evaluation.

Source: C:/Users/austi/Downloads/2610.08902v1.pdf, Agent Plasticity: Measuring Self-Improvement Through Experience, sections 3.5 and 4. The experiments listed here are proposed adaptations for Lean.`;
}

// Slide 6: complete proposed architecture.
{
  const slide = presentation.slides.add();
  slide.background.fill = C.bg;
  addHeader(slide, "Proposed architecture: proof runs and verified memory", 6);
  addText(slide, "A deterministic orchestration script prepares runs and collects evidence. Human review controls the theorem and lessons.",
    70,153,1140,48,{fontSize:20,color:C.gray});

  const positions = [70,305,540,775,1010];
  const labels = ["Monorepo", "Run script", "Agent runs", "Verification", "Comparison"];
  const detail = [
    "Task + tests\nStarting code\nFrozen memory",
    "Prepare files\nRecord settings\nLaunch containers",
    "Stateless\nRetrieved\nCompile and repair",
    "Trusted build\nPlaceholder scans\nSemantic review",
    "Success + cost\nFailure analysis\nDecision records",
  ];
  for(let i=0;i<5;i++) {
    if(i<4) addLine(slide,positions[i]+200,335,positions[i+1],335,C.line,3);
    addBox(slide,positions[i],260,200,190,{fill:i===3?"#DCFCE7":C.white,line:i===3?C.green:C.line});
    addText(slide,labels[i],positions[i]+15,275,170,40,{fontSize:24,bold:true,color:C.navy});
    addText(slide,detail[i],positions[i]+15,330,170,100,{fontSize:20,verticalAlignment:"top"});
  }
  addLine(slide,1110,450,1110,505,C.blue,2);
  addLine(slide,170,505,1110,505,C.blue,2);
  addLine(slide,170,450,170,505,C.blue,2);
  addText(slide,"After both conditions finish: review reusable lessons and update memory for the next experiment",
    195,525,995,65,{fontSize:23,bold:true,color:C.blue,alignment:"center"});
  addText(slide,"Human role: review the target and snapshot, check mathematical meaning, approve reusable lessons",
    70,620,1140,40,{fontSize:20,color:C.navy});
  addFooter(slide,"Completed foundation: verified Lean reduction and artifact protocol. Proposed next step: isolated comparative runs.");
  slide.speakerNotes.text = `The whole system stays in one monorepo. A small orchestration script prepares identical starting workspaces, freezes memory, and launches fresh agent runs. An orchestrator agent is optional.

Each agent writes proofs and logs its decisions. A trusted evaluator checks the exported code, and I review its mathematical meaning. We compare success and cost across the two conditions.

Only after both runs finish do we promote verified lessons into memory for future experiments. The Lean foundation exists. Container orchestration and comparative evaluation are the next steps.

Sources: pipeline/README.md; AGENTS.md; proposed architecture from this research plan`;
}

await fs.mkdir(buildDir, { recursive: true });
for (const [index, slide] of presentation.slides.items.entries()) {
  const png = await presentation.export({ slide, format: "png", scale: 1 });
  await fs.writeFile(path.join(buildDir, `slide-${index + 1}.png`), new Uint8Array(await png.arrayBuffer()));
}
const montage = await presentation.export({ format: "webp", montage: true });
await fs.writeFile(path.join(buildDir, "montage.webp"), new Uint8Array(await montage.arrayBuffer()));

const draft = await PresentationFile.exportPptx(presentation);
await draft.save(draftPath);
await fs.mkdir(validationWorkspace, { recursive: true });
await fs.mkdir(path.dirname(validationDraftPath), { recursive: true });
await fs.mkdir(path.dirname(validationFinalPath), { recursive: true });
await fs.mkdir(path.dirname(validationReceiptPath), { recursive: true });
await fs.copyFile(draftPath, validationDraftPath);

const { finalizePresentation } = await import(pathToFileURL(
  path.join(skillDir, "container_tools", "artifact_tool_utils.mjs")
).href);

const result = await finalizePresentation({
  explicitTotalSlideCount: 6,
  requiredNativeTableOwnerSlides: [],
  requiredNativeChartOwnerSlides: [],
  workspaceDir: validationWorkspace,
  candidatePath: validationDraftPath,
  finalPath: validationFinalPath,
  pythonExecutable,
  integrityValidatorPath: path.join(skillDir, "container_tools", "inspect_presentation_package_integrity.py"),
  layoutValidatorPath: path.join(skillDir, "container_tools", "inspect_presentation_layout_geometry.py"),
  layoutArgs: [
    "--expected-slide-size-emu", "12192000,6858000",
    "--validate-bullet-geometry",
    "--validate-heading-fit",
  ],
  fontPolicy: { basis: "design", families: [FONT] },
  verifyArtifactToolImport: true,
  receiptPath: validationReceiptPath,
});

await fs.copyFile(validationFinalPath, finalPath);
await fs.copyFile(validationReceiptPath, path.join(buildDir, "validation.json"));

console.log(JSON.stringify({ finalPath, result }, null, 2));
