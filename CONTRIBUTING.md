# Contributing to BranchingProcess

The purpose of this library is correct, reusable mathematics. Engineering
simplification must preserve mathematical objects, hypotheses, proof obligations
and the evidence used to verify them.

## Mathematical standards

- Search the pinned Mathlib source and this repository before adding a definition
  or lemma. Scale further research to the semantic risk using
  [Abstraction review](docs/development/ABSTRACTION_REVIEW.md).
- Place an object by its mathematics. Deterministic trees and selection rules,
  measurable operations, probability laws, and model-specific estimates have
  distinct owners. A `MeasurableSpace` assumption or several callers does not
  establish ownership or justify a public abstraction.
- Expose useful general interfaces under the weakest natural hypotheses actually
  proved. Derive special cases from them; remove replaced parallel implementations
  and compatibility aliases. Distinguish a proof restriction from mathematical
  necessity; necessity claims require evidence such as a counterexample.
- Use Mathlib objects for measures, kernels, filtrations, stopping times and path
  laws wherever their semantics fit. A concrete realization must be identified
  with the canonical law instead of maintaining a second law interface.
- Public theorem signatures keep individual mathematical assumptions visible.
  State corrections, stronger hypotheses and unresolved obligations explicitly.
  An assumed target conclusion, unproved input or `sorry` cannot certify a proof.

## Modules and references

Follow the normative [module, namespace and citation conventions](docs/development/MODULE_CONVENTIONS.md).
In particular:

- Namespaces describe mathematical objects and their actual owners; directories
  alone do not create namespaces. Avoid redundant prefixes and compatibility names.
- Headers inventory exact public declarations and explain their mathematics with
  formulas. Cite the full work and exact source result, not “the paper” or “the
  thesis”; use displayed source numbering and never LaTeX source labels in Lean.
- Principal entries stay visible at their subject level. `Lemmas/` contains only
  support without independent reusable meaning. Single-module helpers are private;
  cross-module visibility alone does not make a helper a public mathematical API.
- Each directory has at most one `Lemmas.lean` or `Lemmas/` grouping. Nested proof
  steps may have their own `Lemmas/`. Review directories above eight direct Lean
  files for semantic grouping; keep genuine peer interfaces together when justified.
- Use narrow owner imports. Preserve module visibility and the `import all` rules
  in the detailed conventions; do not expose proof support through umbrella APIs.

[ARCHITECTURE.md](ARCHITECTURE.md) records current owners.
[FORMALIZATION_CHECKLIST.md](FORMALIZATION_CHECKLIST.md) indexes principal theorem
status, assumptions, proof entries and remaining obligations. Neither code size
nor successful compilation alone establishes source correspondence.

## Proofs from references and generalizations

Identify the exact article, book or dissertation and the theorem or proof followed.
Check the same mathematical objects, hypotheses and parameter choices. A local
repair may preserve the strategy; record its mathematical justification and
synchronize maintained exposition only when authorized. If a demonstrated gap
requires a different strategy, obtain the maintainer's agreement before changing it.

When production replaces a reference's special-case proof by a call to a general
result, preserve the original route, including necessary local support, under
`LiteratureProofTest/<CitationKey>/<MathematicalTopic>.lean`. Apply this to earlier
migrations by recovering Git history. Record the full reference/version, exact
result and relevant pages, recovery revision, replacement entry, mathematical
statement, correspondence of proof steps, and any correction or unresolved input.
Calling the replacement theorem does not preserve the reference's argument.
Reusable mathematics stays with its production owner; source-specific support
stays private or in the literature-test namespace. Retain no old-path aliases.

Literature proofs are advisory, distinct from required production and regression
checks. Production and required tests must never import them. Their dedicated
workflow must execute and retain compiler output, dependency versions, axiom
results and source correspondence; failures, cancellations or pending runs must
not block merge through branch protection, required aggregates or job dependencies.
A source-faithful, successfully checked proof is evidence under its stated
assumptions. Failure alone is not proof of an error in a reference. Verified
errors affecting production still require ordinary mathematical review and checks.

## Verification and contributions

Use the [unified verification entry](docs/development/VERIFICATION.md). The reviewed
axiom declarations and permitted axioms have one owner:
`scripts/lean-test-registry.json`. Register new tests there; neither CI YAML nor
literature manifests maintain another expected-declaration list. Missing,
unexpected, ambiguous and unapproved axiom reports remain failures.

Default to affected-module checks for local proof changes. Public mathematical
interfaces, dependency boundaries, check infrastructure and main integration
require full checks. Record measured wall time, child CPU time, toolchain and
commands before optimizing performance. Task counts are not a runtime measure.
Literature checks retain their independent advisory category.

A contribution states the mathematical change, owner, hypotheses, validation
scope and results, and any remaining obligation. Report suspected errors with
an exact source/result and the smallest relevant mathematical or compiler evidence.
Do not describe conditional results as unconditional theorems. Keep dependency
pins coherent; commit neither `.lake/` products nor generated check reports.

Contributions are distributed under the Apache License 2.0; see [LICENSE](LICENSE).
