/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parameters for the diffusive oscillation estimate

This file contains only the deterministic parameter choice used to turn the
explicit truncated fourth-moment estimate into an arbitrarily small error.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- For every positive spatial oscillation and error mass, one can choose a
finite block cover and a truncation level for which the limiting fourth
moment bound is below that mass. -/
theorem exists_proportionalBlockParameters
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {eta : ENNReal} (heta : 0 < eta) :
    ∃ blocks : ℕ, ∃ fraction cutoff threshold : ℝ,
      0 < fraction ∧ 1 < (blocks : ℝ) * fraction ∧
      0 < cutoff ∧ 0 < threshold ∧ 9 * threshold = epsilon ∧
      (blocks : ENNReal) * ENNReal.ofReal
          ((8 * (fraction * cutoff ^ 2) + 3 * fraction ^ 2) /
            threshold ^ 4) < eta := by
  let threshold := epsilon / 9
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    positivity
  by_cases hetaTop : eta = ⊤
  · refine ⟨2, 3 / 4, 1, threshold, by norm_num, by norm_num,
      by norm_num, hthreshold, ?_, ?_⟩
    · dsimp [threshold]
      ring
    · rw [hetaTop]
      exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top ENNReal.ofReal_lt_top
  · let q := eta.toReal
    have hq : 0 < q := ENNReal.toReal_pos (ne_of_gt heta) hetaTop
    let blocks : ℕ := ⌈100 / (q * threshold ^ 4)⌉₊ + 1
    have hblocksNat : 0 < blocks := by
      dsimp [blocks]
      omega
    have hblocks : 0 < (blocks : ℝ) := by exact_mod_cast hblocksNat
    have hblocksLarge : 100 / (q * threshold ^ 4) < (blocks : ℝ) := by
      calc
        100 / (q * threshold ^ 4) ≤
            (⌈100 / (q * threshold ^ 4)⌉₊ : ℕ) := Nat.le_ceil _
        _ < (blocks : ℕ) := by simp [blocks]
    let fraction := 2 / (blocks : ℝ)
    let cutoff := threshold ^ 2 * Real.sqrt q / 100
    have hfraction : 0 < fraction := by
      dsimp [fraction]
      positivity
    have hcover : 1 < (blocks : ℝ) * fraction := by
      dsimp [fraction]
      field_simp
      norm_num
    have hcutoff : 0 < cutoff := by
      dsimp [cutoff]
      positivity
    have hsqrtSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
    have hden : 100 < (blocks : ℝ) * q * threshold ^ 4 := by
      have hqt : 0 < q * threshold ^ 4 := by positivity
      have := (div_lt_iff₀ hqt).mp hblocksLarge
      nlinarith
    have hsecond : 12 / ((blocks : ℝ) * threshold ^ 4) < 12 * q / 100 := by
      rw [div_lt_iff₀ (mul_pos hblocks (by positivity))]
      nlinarith [hden]
    have hreal :
        (blocks : ℝ) *
            ((8 * (fraction * cutoff ^ 2) + 3 * fraction ^ 2) /
              threshold ^ 4) < q := by
      have halgebra :
          (blocks : ℝ) *
              ((8 * (fraction * cutoff ^ 2) + 3 * fraction ^ 2) /
                threshold ^ 4) =
            16 * q / 10000 + 12 / ((blocks : ℝ) * threshold ^ 4) := by
        dsimp [fraction, cutoff]
        field_simp [hblocks.ne', hthreshold.ne']
        nlinarith [hsqrtSq]
      rw [halgebra]
      nlinarith
    refine ⟨blocks, fraction, cutoff, threshold, hfraction, hcover,
      hcutoff, hthreshold, ?_, ?_⟩
    · dsimp [threshold]
      ring
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks),
        ← ENNReal.ofReal_toReal hetaTop]
      exact (ENNReal.ofReal_lt_ofReal_iff hq).2 hreal

end ProbabilityTheory.RandomWalk

end
