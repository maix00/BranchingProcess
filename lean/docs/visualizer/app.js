const state = {
  page: new URLSearchParams(location.search).get("page") || "simulation",
  demo: new URLSearchParams(location.search).get("demo") || "branching-walk",
  selectedObject: new URLSearchParams(location.search).get("object") || "walk-position",
  generation: 7,
  playing: false,
  branchRate: 2.2,
  variance: 1,
  corridorWidth: 0.8,
  corridorSteps: 42,
  seed: 17,
  selectedNode: null,
  timer: null
};

let manifest;

const icons = {
  home: '<svg viewBox="0 0 24 24"><path d="m3 10 9-7 9 7v10a1 1 0 0 1-1 1h-5v-6H9v6H4a1 1 0 0 1-1-1z"/></svg>',
  simulation: '<svg viewBox="0 0 24 24"><circle cx="12" cy="4" r="2"/><circle cx="6" cy="19" r="2"/><circle cx="18" cy="19" r="2"/><circle cx="12" cy="12" r="2"/><path d="M12 6v4M10.5 13.5 7.5 17M13.5 13.5l3 3.5"/></svg>',
  library: '<svg viewBox="0 0 24 24"><path d="M5 3h11a3 3 0 0 1 3 3v14H8a3 3 0 0 1-3-3z"/><path d="M5 17a3 3 0 0 1 3-3h11M8 7h7M8 10h6"/></svg>',
  examples: '<svg viewBox="0 0 24 24"><path d="M8 5v14l11-7zM4 4v16"/></svg>',
  notes: '<svg viewBox="0 0 24 24"><path d="M6 3h12a2 2 0 0 1 2 2v14H4V5a2 2 0 0 1 2-2zM8 8h8M8 12h8M8 16h5"/></svg>',
  external: '<svg viewBox="0 0 24 24"><path d="M14 4h6v6M20 4l-9 9M18 13v5a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h5"/></svg>',
  play: '<svg viewBox="0 0 24 24"><path d="m8 5 11 7-11 7z"/></svg>',
  pause: '<svg viewBox="0 0 24 24"><path d="M8 5v14M16 5v14"/></svg>',
  back: '<svg viewBox="0 0 24 24"><path d="m14 6-6 6 6 6M8 12h10"/></svg>',
  forward: '<svg viewBox="0 0 24 24"><path d="m10 6 6 6-6 6M16 12H6"/></svg>',
  check: '<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="m8 12 2.5 2.5L16 9"/></svg>',
  info: '<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9"/><path d="M12 10v6M12 7.5v.1"/></svg>',
  menu: '<svg viewBox="0 0 24 24"><path d="M4 6h16M4 12h16M4 18h16"/></svg>'
};

const esc = (value) => String(value ?? "").replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;").replaceAll('"', "&quot;").replaceAll("'", "&#039;");
const icon = (name, className = "") => `<span class="icon ${className}">${icons[name] || icons.info}</span>`;
const objectById = (id) => manifest.objects.find((item) => item.id === id) || manifest.objects[0];
const demoById = (id) => manifest.demos.find((item) => item.id === id) || manifest.demos[0];
const sourceUrl = (item) => `${manifest.site.repository}/blob/master/lean/${item.source}`;

function navigate(page, values = {}) {
  state.page = page;
  Object.assign(state, values);
  const params = new URLSearchParams({ page: state.page, demo: state.demo, object: state.selectedObject });
  history.replaceState({}, "", `?${params}`);
  render();
}

function random(seed) {
  let value = (seed >>> 0) || 1;
  return () => {
    value = (1664525 * value + 1013904223) >>> 0;
    return value / 4294967296;
  };
}

function normal(next) {
  const a = Math.max(next(), 1e-7);
  const b = Math.max(next(), 1e-7);
  return Math.sqrt(-2 * Math.log(a)) * Math.cos(Math.PI * 2 * b);
}

function range(values) {
  const min = Math.min(...values);
  const max = Math.max(...values);
  const padding = Math.max((max - min) * 0.14, 1.2);
  return [min - padding, max + padding];
}

function scale(value, domain, target) {
  return target[0] + ((value - domain[0]) / (domain[1] - domain[0])) * (target[1] - target[0]);
}

function makeTree() {
  const next = random(state.seed);
  const levels = [[{ id: "0-0", gen: 0, pos: 0, parent: null }]];
  for (let gen = 1; gen <= 10; gen += 1) {
    const previous = levels[gen - 1];
    const current = [];
    previous.forEach((parent, parentIndex) => {
      const count = Math.max(1, Math.min(4, Math.round(state.branchRate + (next() - 0.5) * 1.7)));
      for (let slot = 0; slot < count; slot += 1) {
        current.push({
          id: `${gen}-${parentIndex}-${slot}`,
          gen,
          pos: parent.pos + normal(next) * state.variance + (slot - (count - 1) / 2) * 0.35,
          parent: parent.id
        });
      }
    });
    levels.push(current);
  }
  const selectedPath = [levels[0][0]];
  for (let gen = 1; gen < levels.length; gen += 1) {
    const parent = selectedPath[selectedPath.length - 1];
    selectedPath.push(levels[gen].find((node) => node.parent === parent.id) || levels[gen][0]);
  }
  return { levels, selectedPath };
}

function branchingSvg(tree) {
  const levels = tree.levels.slice(0, state.generation + 1);
  const nodes = levels.flat();
  const [min, max] = range(nodes.map((node) => node.pos));
  const x = (generation) => scale(generation, [0, 10], [70, 950]);
  const y = (position) => scale(position, [min, max], [430, 56]);
  const lookup = new Map(nodes.map((node) => [node.id, node]));
  const edges = nodes.filter((node) => node.parent && lookup.has(node.parent)).map((node) => {
    const parent = lookup.get(node.parent);
    return `<line class="tree-edge" x1="${x(parent.gen)}" y1="${y(parent.pos)}" x2="${x(node.gen)}" y2="${y(node.pos)}"/>`;
  }).join("");
  const chosen = new Set(tree.selectedPath.slice(0, state.generation + 1).map((node) => node.id));
  const chosenEdges = tree.selectedPath.slice(1, state.generation + 1).map((node) => {
    const parent = lookup.get(node.parent);
    return parent ? `<line class="selected-edge" x1="${x(parent.gen)}" y1="${y(parent.pos)}" x2="${x(node.gen)}" y2="${y(node.pos)}"/>` : "";
  }).join("");
  const circles = nodes.map((node) => {
    const classes = ["tree-node", node.gen === state.generation ? "current" : "", chosen.has(node.id) ? "selected" : "", state.selectedNode === node.id ? "focused" : ""].filter(Boolean).join(" ");
    return `<circle class="${classes}" data-node-id="${esc(node.id)}" cx="${x(node.gen)}" cy="${y(node.pos)}" r="${chosen.has(node.id) ? 6.3 : 5.2}"/>`;
  }).join("");
  const grid = Array.from({ length: 11 }, (_, generation) => `<line class="generation-grid" x1="${x(generation)}" y1="34" x2="${x(generation)}" y2="452"/><text class="axis-label" x="${x(generation)}" y="476" text-anchor="middle">${generation}</text>`).join("");
  return `<svg class="simulation-svg" viewBox="0 0 1020 510" role="img" aria-label="Branching random walk over generations"><g>${grid}</g><g>${edges}${chosenEdges}${circles}</g><text class="axis-title" x="510" y="500" text-anchor="middle">generation</text><text class="legend-label" x="34" y="54">position</text><g class="plot-legend"><circle class="legend-dot neutral" cx="50" cy="86" r="5"/><text x="64" y="90">all particles</text><circle class="legend-dot selected" cx="50" cy="111" r="5"/><text x="64" y="115">selected lineage</text><circle class="legend-dot current" cx="50" cy="136" r="5"/><text x="64" y="140">current generation</text></g></svg>`;
}

function corridorSvg() {
  const next = random(state.seed);
  const values = [0];
  for (let index = 1; index <= state.corridorSteps; index += 1) values.push(values[index - 1] + normal(next) * 0.32);
  const upper = values.map((_, index) => 0.72 + (index > state.corridorSteps * 0.52 ? 0.12 : 0));
  const lower = values.map((_, index) => -0.72 - (index > state.corridorSteps * 0.68 ? 0.1 : 0));
  const path = values.map((value, index) => ({ t: index / state.corridorSteps, value: Math.max(lower[index] + 0.06, Math.min(upper[index] - 0.06, value * state.corridorWidth)) }));
  const x = (t) => 74 + t * 870;
  const y = (value) => 260 - value * 152;
  const line = (series) => series.map((value, index) => `${index ? "L" : "M"}${x(index / (series.length - 1)).toFixed(2)},${y(value).toFixed(2)}`).join(" ");
  const pathLine = path.map((point, index) => `${index ? "L" : "M"}${x(point.t).toFixed(2)},${y(point.value).toFixed(2)}`).join(" ");
  const markers = path.filter((_, index) => index % Math.max(1, Math.floor(state.corridorSteps / 12)) === 0).map((point) => `<circle class="walk-marker" cx="${x(point.t)}" cy="${y(point.value)}" r="3.2"/>`).join("");
  return `<svg class="simulation-svg" viewBox="0 0 1020 510" role="img" aria-label="A random walk inside a finite step corridor"><line class="zero-line" x1="74" y1="260" x2="944" y2="260"/><path class="corridor-upper" d="${line(upper)}"/><path class="corridor-lower" d="${line(lower)}"/><path class="corridor-path" d="${pathLine}"/>${markers}<line class="axis-line" x1="74" y1="414" x2="944" y2="414"/><text class="axis-title" x="510" y="452" text-anchor="middle">normalized time</text><text class="axis-title" x="35" y="262" text-anchor="middle" transform="rotate(-90 35 262)">path value</text><g class="corridor-legend"><line class="corridor-upper" x1="80" y1="52" x2="116" y2="52"/><text x="126" y="56">upper boundary</text><line class="corridor-lower" x1="80" y1="78" x2="116" y2="78"/><text x="126" y="82">lower boundary</text><line class="corridor-path" x1="80" y1="104" x2="116" y2="104"/><text x="126" y="108">sampled path</text></g><g class="energy-readout"><text x="808" y="58">width cost</text><text x="808" y="82" class="energy-value">${(1 / Math.max(state.corridorWidth, 0.1)).toFixed(2)}</text></g></svg>`;
}

function plotDetail() {
  if (state.demo === "branching-walk" && state.selectedNode) {
    const generation = state.selectedNode.split("-")[0];
    return `<span class="detail-kicker">Selected particle</span><strong>address fragment ${esc(state.selectedNode)}</strong><span>generation ${esc(generation)} · optional child slot realized</span>`;
  }
  return `<span class="detail-kicker">Interactive state</span><strong>${state.demo === "corridor" ? "Corridor path" : "Current generation"}</strong><span>${state.demo === "corridor" ? `width = ${state.corridorWidth.toFixed(2)} · ${state.corridorSteps} steps` : `generation ${state.generation} · seeded realization ${state.seed}`}</span>`;
}

function renderPlot() {
  const plot = document.querySelector("[data-simulation-plot]");
  if (!plot) return;
  plot.innerHTML = state.demo === "corridor" ? corridorSvg() : branchingSvg(makeTree());
  document.querySelector("[data-node-detail]").innerHTML = plotDetail();
  plot.querySelectorAll("[data-node-id]").forEach((node) => node.addEventListener("click", () => {
    state.selectedNode = node.dataset.nodeId;
    renderPlot();
  }));
}

function inspector(item) {
  const dependencies = (item.dependencies || []).map((dependency) => `<li>${icon("check", "tiny-check")}<span>${esc(dependency)}</span></li>`).join("");
  const steps = (item.proofSteps || [item.proof]).map((step, index) => `<li><span class="step-index">${index + 1}</span><span>${esc(step)}</span></li>`).join("");
  const related = demoById(state.demo).objects.map(objectById).map((relatedItem) => `<button type="button" class="related-object ${relatedItem.id === item.id ? "selected" : ""}" data-object-id="${esc(relatedItem.id)}"><span>${esc(relatedItem.title)}</span>${icon("forward")}</button>`).join("");
  return `<div class="inspector-heading"><span class="detail-kicker">${esc(item.kind)}</span><h2>${esc(item.title)}</h2><span class="lean-name">${esc(item.leanName)}</span></div><section class="inspector-section"><div class="section-label">Type / statement</div><pre class="statement-block"><code>${esc(item.statement)}</code></pre></section><section class="inspector-section"><div class="section-label">Documentation</div><p class="inspector-copy">${esc(item.summary)}</p><a class="source-link" href="${esc(sourceUrl(item))}" target="_blank" rel="noreferrer">${icon("external")} Open source</a></section><section class="inspector-section proof-section"><div class="proof-heading"><span class="section-label">Proof status</span><span class="status">${icon("check")} ${esc(item.status)}</span></div><p class="inspector-copy">${esc(item.proof)}</p><ol class="proof-steps">${steps}</ol></section><section class="inspector-section"><div class="section-label">Theorem dependencies</div><ul class="dependency-list">${dependencies}</ul></section><div class="related-block"><div class="section-label">This simulation uses</div>${related}</div>`;
}

function controls() {
  const branching = state.demo === "branching-walk";
  return `<div class="control-bar"><div class="transport-group"><button type="button" class="play-button" data-action="toggle-play">${icon(state.playing ? "pause" : "play")}<span>${state.playing ? "Pause" : "Play"}</span></button><span class="control-caption">Step</span><button type="button" class="icon-button" aria-label="Previous step" data-action="previous">${icon("back")}</button><button type="button" class="icon-button" aria-label="Next step" data-action="next">${icon("forward")}</button></div><label class="range-control"><span>${branching ? "Generation" : "Steps"} <output>${branching ? state.generation : state.corridorSteps}</output> <em>${branching ? "/ 10" : ""}</em></span><input type="range" min="${branching ? 0 : 12}" max="${branching ? 10 : 80}" value="${branching ? state.generation : state.corridorSteps}" data-control="${branching ? "generation" : "corridorSteps"}"></label></div><div class="parameter-row">${branching ? `<label class="parameter-control"><span>Branching rate <output>${state.branchRate.toFixed(1)}</output></span><input type="range" min="1" max="3.8" step="0.1" value="${state.branchRate}" data-control="branchRate"></label><label class="parameter-control"><span>Step variance <output>${state.variance.toFixed(1)}</output></span><input type="range" min="0.2" max="2.2" step="0.1" value="${state.variance}" data-control="variance"></label>` : `<label class="parameter-control"><span>Corridor width <output>${state.corridorWidth.toFixed(2)}</output></span><input type="range" min="0.25" max="1.3" step="0.05" value="${state.corridorWidth}" data-control="corridorWidth"></label><label class="parameter-control"><span>Seed <output>${state.seed}</output></span><input type="range" min="1" max="80" value="${state.seed}" data-control="seed"></label>`}</div>`;
}

function simulationPage() {
  const demo = demoById(state.demo);
  if (!demo.objects.includes(state.selectedObject)) state.selectedObject = demo.objects[0];
  const item = objectById(state.selectedObject);
  return `<main class="workspace"><header class="workspace-header"><div><span class="eyebrow">Formal objects / executable views</span><h1>Simulation</h1><p>${esc(demo.description)}</p></div><div class="header-controls"><label>Model<select data-demo-select>${manifest.demos.map((demoItem) => `<option value="${esc(demoItem.id)}" ${demoItem.id === state.demo ? "selected" : ""}>${esc(demoItem.title)}</option>`).join("")}</select></label><label>View<select><option>Positions (1D)</option><option>Genealogy</option><option>Proof dependencies</option></select></label></div></header><div class="workspace-grid"><section class="simulation-column"><div class="plot-frame"><div class="plot-toolbar"><span class="plot-title">${esc(demo.title)}</span><span class="plot-meta">seed ${state.seed} · ${state.demo === "branching-walk" ? `generation ${state.generation}` : `${state.corridorSteps} samples`}</span></div><div data-simulation-plot></div><div class="plot-detail" data-node-detail>${plotDetail()}</div></div>${controls()}</section><aside class="inspector"><div class="inspector-tabs" role="tablist"><button class="inspector-tab active" type="button" data-tab="object" aria-selected="true">Lean object</button><button class="inspector-tab" type="button" data-tab="simulation" aria-selected="false">Simulation</button><button class="inspector-tab" type="button" data-tab="notes" aria-selected="false">Notes</button></div><div class="inspector-body" data-inspector-body>${inspector(item)}</div></aside></div></main>`;
}

function libraryPage() {
  const groups = ["definition", "theorem"].map((kind) => `<section class="library-group"><div class="group-heading"><span class="detail-kicker">${kind === "definition" ? "Objects" : "Theorems"}</span><span>${manifest.objects.filter((item) => item.kind === kind).length} selected</span></div>${manifest.objects.filter((item) => item.kind === kind).map((item) => `<button type="button" class="library-row ${item.id === state.selectedObject ? "selected" : ""}" data-object-id="${esc(item.id)}"><span class="row-kind">${kind === "definition" ? "def" : "thm"}</span><span class="row-content"><strong>${esc(item.title)}</strong><span>${esc(item.summary)}</span></span><span class="row-status">${icon("check")} ${esc(item.status)}</span></button>`).join("")}</section>`).join("");
  return `<main class="workspace"><header class="workspace-header"><div><span class="eyebrow">Selected from manifest.json</span><h1>Lean library</h1><p>Every row is a named declaration chosen for a page or simulation. Open one to inspect its statement and proof notes.</p></div></header><div class="library-layout"><div>${groups}</div><aside class="library-callout"><span class="detail-kicker">Page generation</span><h2>One list, two surfaces</h2><p>The same declaration list feeds the library index and the simulation inspector. Add an entry to the manifest and it appears here automatically after the next build.</p><code>lean/scripts/check-visualizer-manifest.mjs</code></aside></div></main>`;
}

function overviewPage() {
  return `<main class="workspace"><header class="workspace-header"><div><span class="eyebrow">BranchingProcess / visual documentation</span><h1>Formal mathematics, made inspectable</h1><p>Choose a declaration, watch a seeded realization, and follow the bridge back to the Lean source.</p></div><button type="button" class="primary-inline" data-go="simulation">${icon("simulation")} Open simulation</button></header><div class="overview-grid"><section class="overview-hero"><div class="overview-number">${manifest.objects.length}</div><div><span class="detail-kicker">Selected declarations</span><h2>Objects and theorem interfaces</h2><p>The page is driven by a small manifest, so the visible surface can stay curated while the Lean source remains the authority.</p><button type="button" class="text-button" data-go="library">Browse library ${icon("forward")}</button></div></section><section class="overview-list"><div class="group-heading"><span class="detail-kicker">Ready to explore</span><span>${manifest.demos.length} demos</span></div>${manifest.demos.map((demo) => `<button type="button" class="overview-row" data-demo-id="${esc(demo.id)}"><span><strong>${esc(demo.title)}</strong><span>${esc(demo.description)}</span></span>${icon("forward")}</button>`).join("")}</section></div></main>`;
}

function examplesPage() {
  return `<main class="workspace"><header class="workspace-header"><div><span class="eyebrow">Executable intuition</span><h1>Examples</h1><p>Each example is a small browser-side realization attached to formal objects. The numeric state is seeded, so a page can be replayed and discussed.</p></div></header><div class="example-list">${manifest.demos.map((demo) => `<button type="button" class="example-row" data-demo-id="${esc(demo.id)}"><span class="example-mark">${demo.id === "corridor" ? "∿" : "⋮"}</span><span><strong>${esc(demo.title)}</strong><span>${esc(demo.description)}</span></span>${icon("forward")}</button>`).join("")}</div></main>`;
}

function notesPage() {
  return `<main class="workspace"><header class="workspace-header"><div><span class="eyebrow">Reading the formalization</span><h1>Notes</h1><p>Proof objects and simulations answer different questions, so the site keeps them linked but separate.</p></div></header><div class="notes-grid"><article><h2>Kernel-checked layer</h2><p>Definitions, theorem statements, source links, and proof steps come from the selected declaration manifest and are checked against the pinned Lean project in CI.</p></article><article><h2>Computable layer</h2><p>The browser demos use seeded discrete realizations. They illustrate path shape, generation slices, and corridor geometry; they do not claim to execute noncomputable measure-theoretic objects in the browser.</p></article><article><h2>Research status</h2><p>Open asymptotic results stay labeled as interfaces or research targets in the library. A simulation is evidence for intuition, not a proof of the corresponding limit.</p></article></div></main>`;
}

function shell() {
  const navIcon = (id) => id === "overview" ? "home" : id === "library" ? "library" : id === "examples" ? "examples" : id === "notes" ? "notes" : "simulation";
  return `<header class="topbar"><div class="mobile-brand"><button type="button" class="icon-button mobile-menu" aria-label="Open navigation" data-action="toggle-menu">${icon("menu")}</button><span>BranchingProcess</span></div><div class="topbar-context"><strong>${esc(manifest.site.title)}</strong><span>${esc(manifest.site.subtitle)}</span></div><div class="topbar-actions"><button type="button" class="topbar-link" data-go="notes">Workspace ${icon("forward")}</button><a class="icon-button" href="${esc(manifest.site.repository)}" target="_blank" rel="noreferrer" aria-label="Open repository">${icon("external")}</a></div></header><div class="app-body"><aside class="sidebar"><div class="brand-lockup"><span class="brand-mark">B</span><span><strong>BranchingProcess</strong><small>formal lab</small></span></div><nav class="primary-nav" aria-label="Primary navigation">${manifest.navigation.map((item) => `<button type="button" class="nav-item ${item.id === state.page ? "active" : ""}" data-go="${esc(item.id)}">${icon(navIcon(item.id))}<span>${esc(item.label)}</span></button>`).join("")}</nav><div class="sidebar-footer"><span>Mathematics.</span><span>Computation.</span><span>Further together.</span></div></aside>${state.page === "library" ? libraryPage() : state.page === "examples" ? examplesPage() : state.page === "notes" ? notesPage() : state.page === "overview" ? overviewPage() : simulationPage()}</div>`;
}

function bind() {
  document.querySelectorAll("[data-go]").forEach((button) => button.addEventListener("click", () => navigate(button.dataset.go)));
  document.querySelectorAll("[data-demo-id]").forEach((button) => button.addEventListener("click", () => navigate("simulation", { demo: button.dataset.demoId, selectedNode: null })));
  document.querySelectorAll("[data-object-id]").forEach((button) => button.addEventListener("click", () => navigate("simulation", { selectedObject: button.dataset.objectId })));
  const select = document.querySelector("[data-demo-select]");
  if (select) select.addEventListener("change", (event) => navigate("simulation", { demo: event.target.value, selectedNode: null }));
  document.querySelectorAll("[data-action]").forEach((button) => button.addEventListener("click", () => {
    if (button.dataset.action === "toggle-menu") {
      document.querySelector(".sidebar")?.classList.toggle("mobile-open");
      return;
    }
    if (button.dataset.action === "toggle-play") {
      state.playing = !state.playing;
      clearInterval(state.timer);
      if (state.playing) state.timer = setInterval(() => {
        if (state.demo === "branching-walk") state.generation = state.generation >= 10 ? 0 : state.generation + 1;
        else state.corridorSteps = state.corridorSteps >= 80 ? 12 : state.corridorSteps + 1;
        render();
      }, 620);
      render();
    }
    if (button.dataset.action === "previous") {
      if (state.demo === "branching-walk") state.generation = Math.max(0, state.generation - 1);
      else state.corridorSteps = Math.max(12, state.corridorSteps - 1);
      render();
    }
    if (button.dataset.action === "next") {
      if (state.demo === "branching-walk") state.generation = Math.min(10, state.generation + 1);
      else state.corridorSteps = Math.min(80, state.corridorSteps + 1);
      render();
    }
  }));
  document.querySelectorAll("[data-control]").forEach((control) => control.addEventListener("input", (event) => {
    state[event.target.dataset.control] = Number(event.target.value);
    renderPlot();
    const output = event.target.parentElement.querySelector("output");
    if (output) output.textContent = event.target.value;
  }));
  document.querySelectorAll("[data-tab]").forEach((tab) => tab.addEventListener("click", () => {
    document.querySelectorAll("[data-tab]").forEach((item) => item.classList.toggle("active", item === tab));
    document.querySelectorAll("[data-tab]").forEach((item) => item.setAttribute("aria-selected", item === tab ? "true" : "false"));
    const body = document.querySelector("[data-inspector-body]");
    if (tab.dataset.tab === "object") body.innerHTML = inspector(objectById(state.selectedObject));
    if (tab.dataset.tab === "simulation") body.innerHTML = `<div class="inspector-heading"><span class="detail-kicker">Browser state</span><h2>${esc(demoById(state.demo).title)}</h2><span class="lean-name">seed ${state.seed}</span></div><p class="inspector-copy">This panel reports the current realization only. Change a control or click a node to update it.</p><div class="state-list"><span><strong>demo</strong>${esc(state.demo)}</span><span><strong>generation</strong>${state.generation}</span><span><strong>selected object</strong>${esc(objectById(state.selectedObject).title)}</span></div>`;
    if (tab.dataset.tab === "notes") body.innerHTML = `<div class="inspector-heading"><span class="detail-kicker">Scope</span><h2>Proof and simulation</h2></div><p class="inspector-copy">This is a seeded executable example. The theorem status and source link are driven by the declaration manifest and checked separately by Lean.</p>`;
    bindRelated();
  }));
  bindRelated();
}

function bindRelated() {
  document.querySelectorAll(".related-object").forEach((button) => button.addEventListener("click", () => navigate("simulation", { selectedObject: button.dataset.objectId })));
}

function render() {
  document.querySelector("#app").innerHTML = shell();
  bind();
  if (state.page === "simulation") renderPlot();
}

fetch("manifest.json").then((response) => response.json()).then((data) => {
  manifest = data;
  render();
}).catch((error) => {
  document.querySelector("#app").innerHTML = `<div class="error-state"><h1>Could not load manifest</h1><p>${esc(error.message)}</p><p>Serve this folder over HTTP so the browser can load manifest.json.</p></div>`;
});
