# Governance consolidation against the current proof standard

Baseline: `bfdd298e5`, after the advisory dissertation-proof migration. The
external static audit concerned earlier preflight `16be7ba`; it is an input to
this review, not a measurement of the current CI or a replacement standard.
No mathematical statement, hypothesis, Lean proof or LaTeX source is changed.

## Decisions and preserved invariants

- One reviewed declaration registry replaces the ordinary runner's inline map,
  fallback source inventories and CI's repeated expected lists. All 137 names
  previously requested by CI are represented. The initial register covers 159
  required tests and four advisory entries, with 978 expected reports. These
  counts describe this migration, not a quota or a second live inventory.
- The existing axiom parser's missing/extra/duplicate/ambiguity and forbidden-
  axiom checks remain. An explicit empty inventory rejects unexpected reports.
  Category/path drift fails in its own required/advisory scope; duplicate
  registry fields cannot silently overwrite an inventory. Required validation
  and import parsing do not depend on advisory metadata or compiler success.
- The unified front door selects required or advisory checks without merging
  their status semantics. Required code cannot import advisory proofs; no
  required job depends on the advisory workflow. Bibliographic manifests retain
  source correspondence and originating revisions, not another axiom list.
- Contributions retain semantic owners, mathematical headers, exact references,
  natural hypotheses, canonical objects, general-to-special derivation and the
  prohibition of parallel public implementations/compatibility aliases. The
  module/private/`import all` conventions, nested `Lemmas/` limits and proof
  preservation policy remain normative. Full pre-consolidation wording is
  retained in the adjacent snapshots; details live in the development guides.
- Current architecture and principal theorem status are separated from dated
  exploration. Previously unresolved source-level statements are not discharged
  by moving their descriptions. The theorem index keeps the numbered Mogul'skii
  and dissertation boundaries, including explicit remaining obligations.
- Review intensity follows semantic risk. Simple local estimates search pinned
  local APIs; new objects, competing laws, public semantic generalization and
  source-error/strategy claims require the corresponding broader investigation.
  Correctness and useful mathematical generality are required at every level.

## Verification and performance evidence

Check selection includes reverse local imports; removed module names remain
seeds. Public signatures, definitions, module visibility, imports, dependencies,
check machinery and main integration select full checks. The detector is
conservative source analysis, not a mathematical equivalence decision: maintainers
must explicitly escalate unrecognized meaning-changing interfaces.

The migration runs the unified full scope because it changes the check boundary,
then runs the independent literature scope. Reported times are measured per
command with wall and aggregate waited-child CPU seconds, plus pinned revisions,
thread settings and exit statuses. Cache hit/miss is left unmeasured unless the
cache restore/compiler evidence establishes it. No speedup is claimed from task
counts, removal of YAML lines or a comparison to the external static audit.
Runtime reports are generated artifacts rather than manually maintained status
lists; the CI retains them separately from mathematical source-correspondence
reviews. Later optimization should compare equivalent cold/warm workloads.

## Initial measured local run

The full scope passed in the pre-commit working tree based on `106d5239bf9cfefc5622600013eb0fa8a4c0f6ab`
with existing local build products (a warm workload, not a cold-cache benchmark).
Toolchain: `leanprover/lean4:v4.36.0-rc2`; Mathlib: `26573066084e6e2aa8526ea358bc43b66d96f970`.
Workers: 2; `LEAN_NUM_THREADS=2`.

| Step | Wall seconds | Aggregate child CPU seconds | Exit |
| --- | ---: | ---: | ---: |
| tooling | 29.83 | 28.93 | 0 |
| visualizers | 1.78 | 1.80 | 0 |
| build | 2.06 | 2.80 | 0 |
| regressions | 151.33 | 300.46 | 0 |
| imports | 6.58 | 6.47 | 0 |
| style | 3.96 | 3.62 | 0 |

These measurements do not establish a speedup against the old CI. The final
selector/isolation tooling regressions were also rerun after this measurement;
required regressions still cover all 159 modules. CI artifacts supply the
committed-source measurements, including planning and total wall time.
