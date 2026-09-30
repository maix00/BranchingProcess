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

Prefer explicit assumptions over hidden instances. Reuse Mathlib objects for
measures, filtrations, kernels, point measures, and topological spaces. A
formalized theorem should compile from a clean checkout with the pinned
`lean-toolchain` and Lake manifest.

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

For private questions or issues that should not be public, email
**wang_yi_yang@foxmail.com**.

## Local checks

From the repository root:

```sh
lake build
git diff --check
```

For a focused change, use the narrowest target first, for example:

```sh
lake build Probability.Process.IndepIncrements.FiniteDimensional
```

Do not commit `.lake/` build products. Dependency versions are pinned in
`lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`.

Pull requests are checked by the repository's GitHub Actions workflow with the
same pinned toolchain and Lake manifest.

## License and contributions

The repository is distributed under the Apache License 2.0; see
[`LICENSE`](LICENSE). Unless a contribution is explicitly marked otherwise,
submissions are understood to be offered under the same license.
