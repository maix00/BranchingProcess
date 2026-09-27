# Thesis assumption map

The Lean predicates are split by mathematical role:

- `Structural.lean`: at least one child, supercriticality, and the
  permutation-invariant boundary normalization on the raw law;
- `Moments.lean`: the leftmost first, fourth, and positive exponential
  moments, plus the cross-weight condition;
- `Bundles.lean`: small named collections used by the main theorems.

The centered and finite-variance spine assumptions will be stated on the
spine probability law once that law has been constructed. Writing them now as
formal derivatives of a log-Laplace transform would introduce an unnecessary
analytic representation before the many-to-one construction exists.

`HasLeftmostFirstMoment` is parameterized by a `StepLaw`: it first applies the
law's deterministic measurable ordering and only then reads slot zero. No raw
branching law is assumed to arrive ordered. The boundary and cross-weight sums
remain on the raw law because they are invariant under slot permutations. No
general point process is silently assumed to contain a child.

The sorted slot type is abstract. Assumption bundles require a linear locally
finite order with a least element and no greatest element. Mathlib proves that
such an order is order-isomorphic to `ℕ`; `Step/SlotOrder.lean` reuses that
isomorphism to define finite prefixes `firstSlots α N`, proves they contain
exactly `N` slots, and proves that their union exhausts `α`.

## Formalization boundary

The following items are formalized and compile without axioms:

- measurability of slot survival, path survival, displacement, and selected
  positions;
- the ordered point-process enumeration and its many-root marginal laws;
- the finite-population truncation estimate and the analytic implication from
  eventual two-sided bounds to the speed limit;
- the first-moment implication from the fourth-moment assumption.

The following items are still proof obligations for the thesis' main theorems:

- the Mogul'skii small-deviation estimate for the centered spine walk;
- the thesis-specific many-to-one identity after identifying the spine law
  with the centered point-process offspring model (the abstract forward and
  backward measure identities are already formalized in
  `PointProcess/ManyToOne.lean`);
- the branching property at the exploration/stopping-cell level;
- the coupling lemma used for the `a = 0` trajectory argument;
- the probabilistic eventual upper and lower bounds that feed
  `speed_limit_of_eventual_bounds`;
- the full statements of thesis Theorems 1.1 and 1.2, and the one-sided L1
  Theorem 1.3.

Consequently, `BasicBranchingAssumptions`, `TrajectoryMomentAssumptions`, and
`SpeedL1MomentAssumption` are assumption bundles, not theorem proofs. The
analytic file proves only the final deterministic limit once the probabilistic
bounds above are supplied.


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
