# Module, namespace and citation conventions

This is normative detail linked from CONTRIBUTING, not a historical audit.

## Lean module headers and mathematical references

Each Lean module docstring must begin with a list of its public theorem
declarations, using their exact Lean names and a short description. State the
mathematical content with a formula whenever the conclusion is quantitative or
relational; include the essential assumptions in the description. For a
definition, say what object it defines. Keep private proof helpers out of this
list. Update it whenever a public declaration is added, removed, or renamed.

An implementation module under `Lemmas/` should instead label its local
proof-support inventory `## Internal proof declarations`. Give the exact
declaration names and state their defining identity or mathematical role, with
a formula for quantitative or relational statements. This section documents
the proof chain; it does not make those declarations part of the reusable
public API. Keep single-file tactical helpers private and out of the inventory.

When a declaration formalizes or specializes an external result, cite the work
by author and title, identify the exact theorem/lemma/proposition (and section
or page when useful), and give its bibliography key or stable identifier (DOI,
arXiv ID, or URL). For results from a thesis, identify its exact title,
chapter, and displayed theorem number. Do not use `the paper`, `the thesis`,
or `the source` as a substitute for a reference. Apply the same rule to
Mogul'skii's results; for example, identify Theorem 3, Section 4, p. 764 of
the 1974 Russian original
by A. A. Mogul'skii, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765, together
with its English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081. Include the exact Lean theorem name in the module header and
the exact source result in that theorem's docstring.

Avoid source names such as `paper...` in private declaration identifiers.
Name helpers for the mathematical object or proof operation they implement.

Prefer explicit assumptions over hidden instances. Reuse Mathlib objects for
measures, filtrations, kernels, point measures, and topological spaces. A
formalized theorem should compile from a clean checkout with the pinned
`lean-toolchain` and Lake manifest.

Cross-module use triggers a semantic review, not automatic promotion.
Public mathematics must describe a useful operation or result under the weakest
natural assumptions established by its proof. A special model's construction
stays with that model even when several modules call it. Mechanically enlarging
types or deleting assumptions is not, by itself, a useful abstraction.
Use the [risk-based review](ABSTRACTION_REVIEW.md) for the amount of investigation
needed; record pinned dependency APIs for substantive ownership decisions.

## Entry points and supporting lemmas

Keep a principal theorem in a plainly named entry module at the mathematical
subject's directory level. When several files serve only that theorem's proof,
put them under a sibling `Lemmas/` directory, subdivided by mathematical steps
such as `Blocks`, `Entrance`, or `Staircase`. **Files in `Lemmas/` must contain
only helpers that are not independently reusable:** their statements depend on
the specific event, binning, constants, or assembly of that result. A complete
reusable theorem, construction, event definition, or proof technique belongs
in its mathematical subject's directory outside `Lemmas/`, even when the
current result is its only caller. Before moving a file into `Lemmas/`, review
each declaration in it against this rule; split mixed files so reusable
declarations remain outside. A `Lemmas/` directory belongs to one principal
result or a coherent theorem family; do not collect unrelated results in it.

An entry module may import its proof chain, but it must not use `public import`
for modules under `Lemmas/`; reserve that for mathematical dependencies that
belong to the entry module's exposed interface. Keep cross-file proof helpers
in `Lemmas/` as ordinary `lemma` declarations, not `public lemma` or
`theorem`. For files using Lean's `module` syntax, the direct proof caller
should use `import all` for that helper module, never `public import`; this
allows access to proof support without re-exporting it downstream. Legacy
files without `module` syntax cannot use the `all` import modifier, and a
module-syntax file cannot import a legacy module. Until that whole dependency
chain is migrated together, keep both files in the legacy syntax and use plain
`import` for the helper. Do not add `module` solely to obtain `import all`.
If a result needs to be available as a public declaration, move it outside
`Lemmas/` to its mathematical subject. A helper module may import earlier
steps in its own proof chain; those imports do not make the earlier steps
independently reusable.

Proof groupings may be nested when a proof step has its own substantial chain,
including paths such as `FiniteVarianceUpper/Lemmas/JumpPattern/Lemmas/`.
Each `Lemmas/` level continues to hold only non-reusable steps for its parent
result or sub-result. Reusable definitions and theorems move outward to their
semantic owner, even when that means moving them above more than one nested
`Lemmas/` directory. At any one directory level, use at most one direct
`Lemmas.lean` file or one `Lemmas/` directory; group the supporting files
under that single entry rather than creating parallel `Lemmas` groupings.
This use of `Lemmas/` as a marker for non-reusable proof support is a local
repository convention, not a Mathlib naming convention: the
[`Mathlib` source snapshot inspected in the naming audit](https://github.com/leanprover-community/mathlib4/tree/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib)
has no directory named `Lemmas/`. Mathlib organizes source modules by
mathematical subject and can expose reusable lemmas there; never move a
reusable API into this repository's `Lemmas/` directory just because its
current use is proof support.

When a subject directory contains several independent mathematical families,
group the public modules into semantic subdirectories such as `Ordering/`,
`Selection/`, or `PointMeasure/`. Keep the subject level for shared core
definitions and direct entry modules. Do not place a reusable public interface
under `Lemmas/` just to reduce the number of files at the subject level.
Name directories for their mathematical subject or proof role, not for a
parameter value or a sign condition that only selects one theorem instance;
for example, a first-stage population estimate belongs under `FirstStage/`,
with the sign condition stated among the theorem's hypotheses.
Use filenames relative to their semantic directory: prefer
`PointMeasure/Basic.lean` or `Tilted/Law.lean` to repeating the full directory
name in every child filename. Mathlib uses same-level `Foo.lean` and `Foo/`
pairs for deliberate umbrella or entry modules; for example,
[`MeasureTheory/Measure/Dirac.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Dirac.html)
re-exports `Dirac.Def` and `Dirac.Basic`; the same audit snapshot of
[`Mathlib/Tactic/Basify.lean`](https://github.com/leanprover-community/mathlib4/blob/380f2aafb622cb2c1c93dac545b6389083c68c51/Mathlib/Tactic/Basify.lean)
is another substantive entry module beside `Tactic/Basify/`. The same pattern
is allowed here when the root file presents a real interface and the directory
groups related components. Do not add an import-only file merely to re-export
a directory. If a root file and child directory would obscure ownership, put
core declarations in `Basic.lean` or `Core.lean`, or give child modules names
that identify their mathematical roles. Also avoid a direct child file whose
stem repeats its parent directory, such as `Scale/Scale.lean`; use a semantic
name such as `Scale/Basic.lean`. These path choices do not change Lean
declaration namespaces.
Count direct `.lean` files during directory reviews. More than eight is a
review trigger for semantic grouping, not an automatic move: keep a flat
directory only when its modules are genuinely peer interfaces for one subject,
and record that reason in the architecture audit. A large group of independent
interfaces can still be split by the mathematical objects or operations they
describe.

Directory placement communicates which files users should read first; it does
not change Lean declaration visibility. Mark a helper `private` when all its
uses are in its defining module and it is absent from the type of a
module-visible declaration and the body of a module-visible definition. A
private helper may still occur in the proof term of a public theorem. A named
event or construction used in the body of an exported definition must remain
module-visible; list it in the module docstring even when it is specific to
that proof chain. A helper used across proof modules also needs module
visibility, but that alone does not make it a principal public result.
Declare supporting results as `lemma`; principal results may be declared as
`theorem` or `lemma` according to mathematical usage. In Lean, this choice does
not alter visibility or proof behavior: use `private lemma` for same-module
proof steps, and a module-visible `lemma` when another declaration imports it.
The declaration keyword alone does not determine reusability or directory
placement.
The module docstring lists the public declarations required by the header rule
above; directory READMEs or architecture documentation identify the intended
entry modules. When reorganizing a proof tree, update imports and documentation
and build every affected entry module.
