# Ordinary and strong branching at genealogical cuts

Audit date: 2026-11-23. Mathlib revision:
`26573066084e6e2aa8526ea358bc43b66d96f970`.

## Mathematical scope and primary references

For a deterministic ancestry antichain `ell`, ordinary branching identifies,
conditionally on the information outside its descendant region, the descendant
trees with independent canonical trees started at the boundary states. Strong
branching extends that identity to an optional random line `L`, conditioning on
its stopped information `F_L`. A single random generation is one special case;
vertices of an optional line can have different generations in the same sample.

P. Jagers and A. N. Lagerås, *General branching processes conditioned on
extinction are still branching processes* (2008), §2.2–2.3, pp. 542–543,
[DOI:10.1214/ECP.v13-1419](https://doi.org/10.1214/ECP.v13-1419),
[author PDF](https://staff.math.su.se/andreas/ECP-2008-2048.pdf), explicitly
specify the outside-progeny information and state the deterministic product
identity and its optional-line extension. This primary text was read.

J. D. Biggins and A. E. Kyprianou, *Seneta–Heyde norming in the branching
random walk* (1997), §4, p. 348,
[author PDF](https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/BK97.pdf),
state conditional independence at optional lines and attribute the general-type
result to P. Jagers, *General branching processes as Markov fields* (1989),
Theorem 4.14, [DOI:10.1016/0304-4149(89)90075-6](https://doi.org/10.1016/0304-4149(89)90075-6).
Jagers's original full proof remains unavailable in this audit; citing the
restatements does not constitute reading or formalizing that proof.

The distinction is between deterministic and optional **genealogical cuts**.
It is separate from strong Markov branching at chronological stopping times
in a continuous-time model. The latter requires a corresponding process and
adequate state information, which the present discrete state-tree development
does not supply by renaming generation indices.

A random antichain alone is insufficient: its decisions must obey the
optional information condition. Conversely optionality does not require that
membership at a node be determined solely by its own ancestors. Information on
other branches can be available. An ancestral-membership assumption would
specialize the theorem to a smaller class. Optionality of `L` also does not
by itself give optionality of every generation truncation. The implementation
below uses neither extra assumption.

## Native interfaces examined

The pinned Mathlib probability tree contains no stopping-line or branching-law
interface. The official [probability module index](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability.html)
and native stopping-time and conditional-expectation source were checked.

* `IsStoppingTime` / `IsStoppingTime.measurableSpace`: scalar time indices;
  these do not describe unrelated depths on different branches.
* `condExp_stopping_time_ae_eq_restrict_eq_of_countable`: localizes at scalar
  stopping-time fibers. It does not establish equality of information at tree
  cuts or an offspring-tree disintegration.
* `condExp_ae_eq_restrict_of_measurableSpace_eq_on`: requires equality of the
  two information traces. On `{ell subset L}`, the available trace containment
  is only one direction; extra cuts in `L` can suppress information on other
  branches. Assuming trace equality would be an incorrect strengthening.
* `ae_eq_condExp_of_forall_setIntegral_eq`, `setIntegral_condExp`,
  `setIntegral_congr_ae`, and `integral_iUnion`: directly reused for the new
  conditional-identity transfer. Conditional expectation is not redefined.
* Native `iCondIndepFun`, product kernels and infinite product measures remain
  the target interfaces for conditional independence and descendant-tree laws.
  Their availability does not prove the model's conditional product identity.

## Implemented information and transfer results

`Process/Tree/Line/Information/Localization.lean` proves:

1. The optional random set `L` is measurable in `F_L`, even without countability
   of its range or of the address space.
2. For a countable node set `ell`, `{ell subset L}` is in `F_L`.
3. For a countable deterministic line `ell`, that containment event is in
   `F_ell`, and `A in F_L` implies `A intersect {ell subset L} in F_ell`.

The proof tests optionality against the existing `Line.firstEntrance` of a
union of the test cut with individual strict prefixes. It does not introduce
another cut or truncation definition. The reusable deterministic identity
`Line.precedes_firstEntrance_iff` is owned by `Combinatorics/UlamHarris/Line/FirstEntrance.lean`.
Single-module support proofs stay private in their owner; no cross-module
implementation lemmas or unnecessary `Lemmas/` directory are introduced.

`Process/Tree/Line/ConditionalExpectation.lean` transfers deterministic-cut
conditional identities to a stopped-information-measurable choice from a
countable family of countable cuts contained in `L`. Only the **tested family**
is countable; `L` can have unbounded depth and uncountably many possible values.
For countable addresses this permits testing finite tuples on `L`. Integrability
of the deterministic and selected payoffs and stopped strong measurability of
the selected candidate integral are explicit. This theorem is a transfer of
conditional identities, not a construction or proof of a branching law.

`Information/Boundary.lean` proves birth-event and selected-state stopped
measurability for the general coordinate information. The actual generation
observations are implemented in `BranchingProcess/State/Observation/Basic.lean`;
`Observation/Line.lean` proves their birth measurability from the parent's
family, observes their selected boundary states, and supplies the actual boundary states to the product-tree kernel. Native kernel
integration provides strong measurability of its integrals.
The same module proves that the deterministic generation cut's information is
exactly native `Filtration.piLE`. These results allow arbitrary measurable state
spaces and arbitrary root and child-address types; a selected address must have
countable range. No branching independence is assumed in these measurability
proofs.

## Completed canonical law and specializations

The canonical discrete state-dependent offspring-kernel model now has the
ordinary and strong branching laws, proved from its actual generation-path law.

* `State/Observation/Complement.lean` identifies singleton-cut information with
  the past generations and all other subtrees at that generation.
* `State/Descendants/SingleNode.lean` derives the one-node outside-subtree
  conditional law from `descendantTrees_jointLaw`. The general kernel coordinate
  theorem splits off one coordinate of the native infinite product kernel.
* `State/Descendants/Products.lean` proves ordinary branching at arbitrary
  deterministic finite antichains, including mixed depths. It uses
  `MeasureTheory.condExp_finsetProd_of_complement`; sibling birth states may be
  correlated under the offspring kernel.
* `State/StrongBranching.lean` is the public optional-line entry. Localization
  proves the product identity on `{ell subset L}`, including samples with empty
  lines and random line cardinality. No global enumeration of `L` is needed.
  For an observable injective indexed family of nodes on `L`, each address
  having countable range, it constructs the native product kernel and proves
  `HasCondDistrib` for the entire family of complete descendant trees.
  The index type itself need not be countable. The conditional expectation
  formula accepts arbitrary integrable strongly measurable Banach-valued tests.
* `State/Descendants/Observed.lean` derives the existing deterministic-generation,
  history-selected-generation and stopping-generation conclusions from that
  public interface. The stopping case uses Mathlib's countable stopping-time
  localization. The former independent selected-descendant proof is removed;
  the original signatures and assumptions are retained.

`Kernel.hasCondDistrib_of_condExp_generator` identifies a supplied Markov
kernel using conditional expectations on a generating pi-system and native
finite-measure uniqueness. It does not invoke existence of regular conditional
distributions, and introduces no standard-Borel hypothesis. Native product
kernels, `HasCondDistrib`, kernel integration, conditional expectation and
stopping-time localization are reused rather than redefined.

There is no countable-range, bounded-depth, coverage, ancestor-only membership,
moment or order restriction on the optional line. Initial root states have an
arbitrary joint law. State spaces and address types retain the measurable
generality of the canonical model. This completes the discrete offspring-kernel
version of the conditional identities stated by Jagers–Lagerås; it does not
claim to formalize the original continuous-time life-history construction.

## Validation

The optional-line regression includes a deterministic antichain with nodes at
depths one and two, localized against an arbitrary optional line. Its product
formula remains meaningful when that line is empty. Public law, information
and transfer results are included in the explicit axiom audit, alongside the
existing stopping-generation and spine consumers.

Validated on 2026-11-23:

* `LEAN_NUM_THREADS=2 lake build`: successful, 11957 jobs.
* `OptionalLineFiltration.lean`, `State/Kernel.lean`,
  `SpineDisintegration.lean`, and `SpinalBias.lean`: compiled; all 92
  configured axiom reports contain only the reviewed standard Lean axioms.
* Mathlib style lint and the project import-boundary audit: successful.
* The build/test infrastructure's 32 Python unit tests: successful.

## Review of the completed optional-line interface

Commit `81816fc3e` was reviewed against Jagers–Lagerås (2008), §2.2–2.3,
including the empty-product convention in (1). The proof chain uses the
canonical `generationPathLaw` and `treeKernel`: the full generation subtree
joint law gives the singleton outside-subtree law, native tower and pull-out
identities give deterministic-cut products, and stopped-information
localization gives the optional-cut identities. This verifies the discrete
kernel statement of the cited identity. Jagers (1989), Theorem 4.14, is the
attributed original result; its full proof was not available for line-by-line
comparison.

The review additionally compared the pinned `HasCondDistrib`, `condDistrib`,
`iCondIndepFun`, `condExpKernel`, product-measure and conditional-expectation
APIs with the official Mathlib documentation. Native `iCondIndepFun` is defined
through `condExpKernel` and requires a Standard Borel sample space at this
revision. The explicit product `HasCondDistrib` theorem retains arbitrary
measurable states and roots, so it remains the principal interface here.
No second independence predicate or regular-conditional-law construction is
introduced. The finite-product and supplied-kernel uniqueness extensions
bridge native integration and measure uniqueness; the pinned library has no
matching arbitrary-measurable-space optional-line theorem.

Ownership and visibility were checked declaration by declaration. Coordinate
information and conditional-identity transfer belong to `Process.Tree.Line`;
state observations and actual branching laws belong to `BranchingProcess.State`;
conditional integration and finite-product operations belong to `Kernel` and
`MeasureTheory`, respectively. These are independently reusable mathematical
results, so they stay outside `Lemmas/`. Single-file tactical helpers are
`private`; there is no non-reusable cross-file assembly requiring an additional
`Lemmas/` directory. `State/` has seven direct Lean files, `Descendants/` six,
and `Observation/` three. Each new module's header inventories its public
formulas and hypotheses.

The regression now constructs an actual random cut: according to an observed
initial Boolean state it is either empty or consists of two vertices at depths
one and two. The localized strong branching identity is checked on exactly
that initial decision event. This exercises random cardinality, empty lines,
mixed depths and a state-dependent offspring kernel without an enumeration of
the random line. Import guards now enforce the separation of generic line
information, generic integration, state-kernel branching and BRW/spine models.
The README's obsolete claim that optional-line strong branching remained open
was removed; its remaining boundaries agree with the checklist.

Review validation: the full 11,957-job library build, all 150 Lean tests,
32 Python tests, Mathlib style lint over 1,788 modules and the strengthened
import-boundary audit passed. The new random-cut axiom reports contain only
`propext`, `Classical.choice` and `Quot.sound`.
