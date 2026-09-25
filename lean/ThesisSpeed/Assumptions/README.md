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
`HasOrderedOffspring` and `HasAtLeastOneChild`. No general point process is
silently assumed to contain a child.
