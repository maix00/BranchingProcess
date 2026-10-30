/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parameters of the second-stage affine tube

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveASecondStageSlope`:
  \(d_D=\kappa c^{-2}D^{-2/3}\).
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveASecondStageWidth`:
  \(w_D=cD^{1/3}\).
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveASecondStageEntranceScale`:
  the entrance margin \(e_D=(5\kappa/c^2+v)D^{1/3}/2\).
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveASecondStageBridgeScale`:
  the bridge displacement scale \(b_k=(v-\kappa/c^2)k^{1/3}/24\).

The public definitions are
\[
  d_D=\frac{\kappa}{c^2}D^{-2/3},\qquad
  w_D=cD^{1/3},\qquad
  e_D=\frac{5\kappa/c^2+v}{2}D^{1/3},\qquad
  b_k=\frac{v-\kappa/c^2}{24}k^{1/3}.
\]
They give the slope, width, entrance scale, and stable bridge scale used by the
second-stage corridor.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

/-- The slope of the second-stage affine tube. -/
noncomputable def positiveASecondStageSlope
    (κ c : ℝ) (D : ℕ) : ℝ :=
  κ / c ^ 2 * ((D : ℝ) ^ ((-2 : ℝ) / 3))

/-- The width of the second-stage affine tube. -/
noncomputable def positiveASecondStageWidth
    (c : ℝ) (D : ℕ) : ℝ :=
  c * ((D : ℝ) ^ ((1 : ℝ) / 3))

/-- The entrance scale used to join a finite-variance entrance block to the
downward bridge in the second-stage tube. -/
noncomputable def positiveASecondStageEntranceScale
    (κ c v : ℝ) (D : ℕ) : ℝ :=
  ((5 * (κ / c ^ 2) + v) / 2) * ((D : ℝ) ^ ((1 : ℝ) / 3))

/-- The stable endpoint-bridge scale used by the second-stage corridor
estimate. -/
noncomputable def positiveASecondStageBridgeScale
    (κ c v : ℝ) (k : ℕ) : ℝ :=
  ((v - κ / c ^ 2) / 24) * ((k : ℝ) ^ ((1 : ℝ) / 3))


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
