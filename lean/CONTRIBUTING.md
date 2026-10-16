# Contributing to BranchingProcess

Thank you for helping build this formalization. Mathematical corrections,
small reusable lemmas, better module boundaries, documentation, and examples
are all useful contributions.

## Before you start

1. Search Mathlib and the existing library before introducing a new definition.
2. Read [`ARCHITECTURE.md`](ARCHITECTURE.md) and place a result in the lowest
   layer that does not depend on the thesis-specific construction.
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
declarations, using their exact Lean names and a short description. Keep private
proof helpers out of this list. Update it whenever a public declaration is
added, removed, or renamed.

When a declaration formalizes or specializes an external result, cite the work
by author and title, identify the exact theorem/lemma/proposition (and section
or page when useful), and give its bibliography key or stable identifier (DOI,
arXiv ID, or URL). For results from a thesis, identify its exact title,
chapter, and displayed theorem number. Do not use `the paper`, `the thesis`,
or `the source` as a substitute for a reference. Apply the same rule to Mogul'skii's results;
for example, cite Theorem 3, Section 4, p. 764 of A. A. Mogul'skii,
"Small Deviations in a Space of Trajectories" (Russian original, 1974; English
translation, *Theory of Probability and Its Applications* 19(4) (1975),
726–736, DOI 10.1137/1119081). Include the exact Lean theorem name in the
module header and the exact source result in that theorem's docstring.

Avoid source names such as `paper...` in private declaration identifiers.
Name helpers for the mathematical object or proof operation they implement.

Prefer explicit assumptions over hidden instances. Reuse Mathlib objects for
measures, filtrations, kernels, point measures, and topological spaces. A
formalized theorem should compile from a clean checkout with the pinned
`lean-toolchain` and Lake manifest.

## Entry points and proof modules

Keep a principal theorem in a plainly named entry module at the mathematical
subject's directory level. When several files serve only that theorem's proof,
put them under a sibling `Proof/` directory, subdivided by mathematical steps
such as `Blocks`, `Entrance`, or `Staircase`. Keep genuinely reusable definitions
and theorems in their own semantic directories instead of moving them into a
particular result's `Proof/` tree. Avoid a catch-all `Lemmas/` directory whose
contents have unrelated mathematical roles.

Directory placement communicates which files users should read first; it does
not change Lean declaration visibility. Mark a helper `private` when all its
uses are in its defining module. A helper used across proof modules may need
module visibility, but that alone does not make it a principal public result.
The module docstring lists the public declarations required by the header rule
above; directory READMEs or architecture documentation identify the intended
entry modules. When reorganizing a proof tree, update imports and documentation
and build every affected entry module.

## Issues and questions

Open an issue for a suspected mathematical error, a missing measurability
argument, a dependency or naming problem, a reproducible build failure, or a
theorem you would like to formalize. Include the relevant module, Lean and
Mathlib revisions, the command that fails, and the smallest useful error
excerpt. Counterexamples and references to the original paper are especially
helpful.

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
