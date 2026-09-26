# Thesis assumption map

The Lean predicates are split by mathematical role:

- `Structural.lean`: ordered representation, at least one child,
  supercriticality, and boundary normalization;
- `Moments.lean`: the leftmost first, fourth, and positive exponential
  moments, plus the cross-weight condition;
- `Bundles.lean`: small named collections used by the main theorems.

The centered and finite-variance spine assumptions will be stated on the
spine probability law once that law has been constructed. Writing them now as
formal derivatives of a log-Laplace transform would introduce an unnecessary
analytic representation before the many-to-one construction exists.

`HasLeftmostFirstMoment` refers to slot zero only together with
`HasOrderedSlots` and `HasAtLeastOneChild`. No general point process is
silently assumed to contain a child.

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
