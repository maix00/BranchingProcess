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

- `LiteratureProofTest.Wang2026AsymptoticSpeed.positiveASecondStageSlope`:
  \(d_D=\kappa c^{-2}D^{-2/3}\).
- `LiteratureProofTest.Wang2026AsymptoticSpeed.positiveASecondStageWidth`:
  \(w_D=cD^{1/3}\).
-/

@[expose] public section

namespace LiteratureProofTest.Wang2026AsymptoticSpeed


open Asymptotics

/-- The slope of the second-stage affine tube. -/
noncomputable def positiveASecondStageSlope
    (κ c : ℝ) (D : ℕ) : ℝ :=
  κ / c ^ 2 * ((D : ℝ) ^ ((-2 : ℝ) / 3))

/-- The width of the second-stage affine tube. -/
noncomputable def positiveASecondStageWidth
    (c : ℝ) (D : ℕ) : ℝ :=
  c * ((D : ℝ) ^ ((1 : ℝ) / 3))

end LiteratureProofTest.Wang2026AsymptoticSpeed
