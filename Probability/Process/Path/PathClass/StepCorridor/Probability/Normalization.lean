/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Mogulskii rate normalization

The process escape rate is naturally stated for a half-width-one tube. The
following coefficient converts that convention to the source's width-energy
normalization and is independent of a particular process construction.
-/

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

/-- Convert a negative half-width-one escape constant to the coefficient for
the source's full-width energy normalization. -/
noncomputable def rateCoefficient (α escapeConstant : ℝ) : ℝ :=
  -(escapeConstant * 2 ^ α)

theorem rateCoefficient_pos {α escapeConstant : ℝ}
    (hEscape : escapeConstant < 0) :
    0 < rateCoefficient α escapeConstant := by
  rw [rateCoefficient]
  have hpow : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  exact neg_pos.mpr (mul_neg_of_neg_of_pos hEscape hpow)

end ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

end
