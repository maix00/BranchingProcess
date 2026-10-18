# Contributing to BranchingProcess

Thank you for helping build this formalization. Mathematical corrections,
small reusable lemmas, better module boundaries, documentation, and examples
are all useful contributions.

## Before you start

1. Search the pinned Mathlib source and the existing library before introducing
   a new definition. When the abstraction boundary is unclear, inspect the
   current official Mathlib documentation/source and relevant mathematical
   references as well; then check that the candidate API exists in the pinned
   revision used by this repository. Network results inform the design, while
   the pinned dependencies determine what the implementation can use.
2. Read [`ARCHITECTURE.md`](ARCHITECTURE.md) and place a result in the lowest
   layer that does not depend on the specific construction being formalized.
3. Import narrow modules. Do not add a catch-all aggregate import just to make
   a declaration available.
4. Check the proof boundary in
   [`FORMALIZATION_CHECKLIST.md`](FORMALIZATION_CHECKLIST.md) before describing
   a result as complete.

## Pull requests

Keep a pull request focused on one mathematical or architectural change.
Include:

- the statement and assumptions of each new theorem;
- a short explanation of why the definition belongs in its module;
- a targeted `lake build` command, or the full build when the dependency
  boundary changed;
- documentation updates when a theorem moves from an open obligation to a
  verified result, or when a path is renamed.

## Lean module headers and mathematical references

Each Lean module docstring must begin with a list of its public theorem
declarations, using their exact Lean names and a short description. State the
mathematical content with a formula whenever the conclusion is quantitative or
relational; include the essential assumptions in the description. For a
definition, say what object it defines. Keep private proof helpers out of this
list. Update it whenever a public declaration is added, removed, or renamed.

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

Cross-module use alone does not justify moving a declaration to a more general
public layer. It triggers an abstraction review. For every proposed promotion
or outward move, search the pinned Mathlib source and repository, inspect the
official Mathlib documentation and relevant dependencies online, and consult
the mathematical literature when it can identify a more general statement.
Compare the weakest natural assumptions and the exact semantics, not just
similar names. Add a public abstraction only when it states a meaningful
reusable mathematical operation or theorem beyond a thin restatement of an
existing API. A module having several clients is a reason to audit its
abstraction, not evidence by itself that the declaration belongs at a higher
level. Record the sources and exact candidate statements examined, compare
their assumptions and conclusions with the actual use sites, and explain why
the chosen statement is the most general useful one and belongs at that
semantic layer. Identify the pinned revision for every dependency API checked.
Keep model-specific names and corollaries with their owning subject.

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

An entry module may import its proof chain, but it should use ordinary
`import` for modules under `Lemmas/`; reserve `public import` for mathematical
dependencies that belong to the entry module's exposed interface. This keeps
proof-only helper declarations from appearing as re-exported API. A helper
module may import earlier steps in its own proof chain, but those imports do
not make the earlier steps independently reusable.

Proof groupings may be nested when a proof step has its own substantial chain,
including paths such as `FiniteVarianceUpper/Lemmas/JumpPattern/Lemmas/`.
Each `Lemmas/` level continues to hold only non-reusable steps for its parent
result or sub-result. Reusable definitions and theorems move outward to their
semantic owner, even when that means moving them above more than one nested
`Lemmas/` directory. At any one directory level, use at most one direct
`Lemmas.lean` file or one `Lemmas/` directory; group the supporting files
under that single entry rather than creating parallel `Lemmas` groupings.

When a subject directory contains several independent mathematical families,
group the public modules into semantic subdirectories such as `Ordering/`,
`Selection/`, or `PointMeasure/`. Keep the subject level for shared core
definitions and direct entry modules. Do not place a reusable public interface
under `Lemmas/` just to reduce the number of files at the subject level.
Use filenames relative to their semantic directory: prefer
`PointMeasure/Basic.lean` or `Tilted/Law.lean` to repeating the full directory
name in every child filename. Mathlib permits a same-level `Foo.lean` and
`Foo/` when the file is a substantive entry interface and the directory holds
its components. This repository uses a stricter discoverability rule: do not
place `Foo.lean` beside `Foo/`; put core declarations in `Basic.lean` or
`Core.lean`, or give child modules names that identify their mathematical
roles. Also avoid a direct child file whose stem repeats its parent directory,
such as `Scale/Scale.lean`; use a semantic name such as `Scale/Basic.lean`.
These path choices do not change Lean declaration namespaces. Do not add a
same-name file merely to re-export a directory.
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

## Issues and questions

Open an issue for a suspected mathematical error, a missing measurability
argument, a dependency or naming problem, a reproducible build failure, or a
theorem you would like to formalize. Include the relevant module, Lean and
Mathlib revisions, the command that fails, and the smallest useful error
excerpt. For mathematical claims, give a complete bibliographic reference and
the exact theorem, lemma, equation, or page that supports it.

Pull requests are welcome even when they formalize only an intermediate lemma.
If a proposed statement is not yet proved, label it as an interface or open
obligation instead of weakening the assumptions silently.

## Local checks

From the repository root:

```sh
lake build
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/run-all-lean-tests.py
python3 scripts/check-lean-import-boundaries.py
python3 scripts/run-mathlib-lint-style.py
git diff --check
```

For a focused change, use the narrowest target first, for example:

```sh
lake build Probability.Process.IndepIncrements.FiniteDimensional
```

Do not commit `.lake/` build products. Dependency versions are pinned in
`lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`.

Pull requests are checked by the repository's GitHub Actions workflow with the
same pinned toolchain and Lake manifest. `run-mathlib-lint-style.py` invokes
Mathlib's own `lint-style` over every project source module. The no-argument
Mathlib command selects the Lake target name `BranchingProcess`, which is not a
Lean source module in this repository, so the wrapper supplies the module names.

## License and contributions

The repository is distributed under the Apache License 2.0; see
[`LICENSE`](LICENSE). Unless a contribution is explicitly marked otherwise,
submissions are understood to be offered under the same license.
