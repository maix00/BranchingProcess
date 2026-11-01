# Assumption map for *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*

The Lean predicates are split by mathematical role:

- `Probability/BranchingProcess/Offspring/Count.lean`: child-count law,
  expected extended child count, almost-sure nonemptiness, and
  supercriticality for a probability offspring law;
- `Structural.lean`: permutation-invariant boundary normalization on the raw
  branching-walk law;
- `Moments.lean`: the leftmost first, fourth, and positive exponential
  moments;
- `CrossWeight.lean`: the permutation-invariant pair-weight integrability
  condition on the raw optional-slot law.

The predicates above remain reusable abstractions for individual mathematical
conditions. The theorem interfaces pass the conditions they use as separate
hypotheses; they are not combined into assumption structures.

The centered and finite-variance spine assumptions will be stated on the
spine probability law once that law has been constructed. Writing them now as
formal derivatives of a log-Laplace transform would introduce an unnecessary
analytic representation before the many-to-one construction exists.

`HasLeftmostFirstMoment` is parameterized by a `StepLaw`: it first applies the
law's deterministic measurable ordering and only then reads slot zero. No raw
branching law is assumed to arrive ordered. The boundary and cross-weight sums
remain on the raw law because they are invariant under slot permutations. No
general point process is silently assumed to contain a child.

The sorted slot type is abstract. The relevant theorem interfaces require a
linear locally finite order with a least element and no greatest element.
Mathlib proves that such an order is order-isomorphic to `ℕ`;
`Step/SlotOrder.lean` reuses that isomorphism to define finite prefixes
`firstSlots α N`, proves they contain exactly `N` slots, and proves that their
union exhausts `α`.

## Formalization boundary

The current status of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Theorems 1.1–1.3 is maintained in
[`FORMALIZATION_CHECKLIST.md`](../../../FORMALIZATION_CHECKLIST.md). That checklist
is the source of truth for theorem-level completion and remaining proof
obligations; this file records the meaning and ownership of the assumptions.

In particular, the finite-variance endpoint sublevel estimate and its
law-preserving transfer to the common countable-root field are formalized
under explicit scale, moment, and exponent-gap hypotheses in
`Probability/BranchingRandomWalk/Selection/NSelection/EndpointDeviation/Endpoint/Sequence/FiniteVariance.lean`.
The endpoint moment bounds and the generic polynomial-tail criterion for
`L²` convergence are also available. The remaining work is in assembling
these interfaces into the full flat theorem statements, proving the
positive-start and zero-start endpoint bounds required by Theorem 1.1, and
completing the exact-finite-`N` speed application for Theorem 1.2. The
checklist records the precise status of each dependency.

The main theorem interfaces continue to expose their assumptions separately;
these intermediate estimates do not replace them with a bundled assumption
structure. Deterministic convergence conclusions use Mathlib's
`Filter.tendsto_order` directly rather than a project wrapper that restates
that criterion.


## Abstract marks and the real displacement potential

The step layer does not identify the mark space with `ℝ`. A measurable
`Potential X` projects abstract marks to the scalar displacement used by
ordering and exponential point-process functionals. When marks themselves
form the additive displacement space, the theorem interface uses
`AdditivePotential X`, namely a measurable additive homomorphism `X →+ ℝ`.
The proved `AdditivePotential.map_list_sum` lemma states that projecting the
sum of edge displacements equals summing their projected values. The
one-dimensional model is recovered by `realAdditivePotential`.

Ordering is expressed by `Step.IsOrderedBy φ`: the step retains its complete
`X`-valued marks and is ordered only after projection. Thus neither an order
on `X` nor injectivity of `φ` is required. Equal potential values retain
separate child slots and therefore retain multiplicity in cross terms.
