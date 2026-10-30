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

The following items are formalized and compile without axioms:

- measurability of slot survival, path survival, displacement, and selected
  positions;
- the ordered point-process enumeration and its many-root marginal laws;
- the finite-population truncation estimate; the elementary squeeze from
  eventual two-sided bounds uses Mathlib's order-topology criterion
  `Filter.tendsto_order` directly;
- the first-moment implication from the fourth-moment assumption.

The following items are still proof obligations for Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Theorems 1.1–1.3:

- the Mogul'skii small-deviation estimate for the centered spine walk;
- the many-to-one identity needed for Wang Yiyang's Theorem 1.1 after
  identifying the spine law with the centered point-process offspring model
  (the abstract tilt and
  forward/backward endpoint identities are already formalized in
  `Probability/PointProcess/Tilted.lean` and
  `Probability/BranchingRandomWalk/Spine/PointMeasure/Endpoint.lean`);
- the branching property at the exploration/stopping-cell level;
- the coupling lemma used for the `a = 0` trajectory argument;
- the probabilistic eventual upper and lower bounds that feed the final speed
  limit through Mathlib's order-topology convergence criterion;
- the full statements of Theorems 1.1 and 1.2, and the one-sided L1
  Theorem 1.3.

The final deterministic implication applies Mathlib's
`Filter.tendsto_order` directly once the probabilistic bounds above are
supplied. There is no separate project theorem restating that criterion. The
intermediate estimates do not change the assumption list in the main theorem
statements.


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
