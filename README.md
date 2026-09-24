# Lean verification of the speed theorem

Run `lake build ThesisSpeed` in this directory. This project uses the local
mathlib checkout at `../../../mathlib4` and Lean `v4.26.0-rc2`.

`ThesisSpeed/Analytic.lean` currently verifies two analytic facts relevant to the new
Theorem 1.3:

1. A pointwise truncation inequality for controlling an exceptional event with
   a first moment in place of a fourth-moment/Cauchy--Schwarz estimate.
2. The exact final limit of the speed from eventual upper and lower bounds at
   every positive error, with coefficient `Real.pi ^ 2 * σ2 / 2`.

This is **not a formal proof of Theorem 1.3**. The following are still missing:

- a Lean definition of the offspring point process, selected branching random
  walk, and almost-sure speed;
- the many-to-one formula and the Mogul'skii small-deviation estimates;
- the couplings that yield the two eventual bounds under a first moment;
- an argument replacing the cross-pair second moment, if the cross-term
  assumption is also to be weakened.

Theorem 1.1 retains its stated fourth-moment assumption and its `L²` claim.
Theorem 1.3 currently retains the cross-term assumption. No assumption is
silently promoted to a verified Lean result.
