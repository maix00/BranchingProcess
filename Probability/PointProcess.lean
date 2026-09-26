import Probability.PointProcess.Basic

/-!
# Point-process layer

The abstract point process: a measurable map from a sample space to counting
measures that are finite on a chosen family of sets. The family is a
parameter, so local finiteness, left-ray finiteness, and the paper's
half-line condition are instances rather than built-in assumptions.

This is the probability-theoretic object itself and lives under
`Probability/`, mirroring Mathlib's convention that a named stochastic-process
family gets its own top-level directory under `Mathlib/Probability/` (compare
`Probability/BrownianMotion/` and `Probability/Martingale/`). The realization
by a branching-step field, together with its enumeration, ranked
representation, and multi-root law, belongs to the branching random walk and
lives in `Probability/BranchingRandomWalk/PointProcess/`.
-/
