/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-!
# Real parameters for the left-tail estimate

This file isolates the deterministic parameter choices in the proof of the
polynomial left-tail estimate.  The probabilistic drawdown estimate is kept
separate: these lemmas only use the strict gap between the target level and
the Brownian rate.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

/-- If the endpoint level is strictly below the diffusive rate, choose an
intermediate level above both the target and `-a`. -/
theorem exists_leftTailIntermediateLevel
    {a t C zeta : ℝ} (ht : 0 < t) (hC : 0 < C)
    (hzeta : zeta < -a + C * t) :
    ∃ zeta0 : ℝ, max zeta (-a) < zeta0 ∧ zeta0 < -a + C * t := by
  have hbase : -a < -a + C * t := by
    have hprod := mul_pos hC ht
    linarith
  exact exists_between (max_lt hzeta hbase)

/-- Given an intermediate endpoint level strictly above `-a` and below the
diffusive rate, choose the corridor parameters used in (4.16).  In addition to
`b > 1`, `0 < d < C`, and `c = b / (b + a + zeta0) ∈ (0,1)`, the result records
the strict exponent margin needed to choose a polynomial tail power
`epsilon`. -/
theorem exists_leftTailExponentParameters
    {a t C zeta0 : ℝ} (ht : 0 < t) (hC : 0 < C)
    (hzeta0Lower : -a < zeta0)
    (hzeta0Upper : zeta0 < -a + C * t) :
    ∃ b d c epsilon : ℝ,
      1 < b ∧ 0 < d ∧ d < C ∧
      c = b / (b + a + zeta0) ∧ 0 < c ∧ c < 1 ∧
      0 < epsilon ∧ epsilon < b - 1 ∧
      epsilon < d * t / b ^ 2 - (a + zeta0) := by
  let q : ℝ := a + zeta0
  have hq : 0 < q := by dsimp [q]; linarith
  have hqt : q < C * t := by dsimp [q]; linarith
  let d : ℝ := (q / t + C) / 2
  have hqdiv : q / t < C := (div_lt_iff₀ ht).2 (by simpa [mul_comm] using hqt)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdC : d < C := by dsimp [d]; linarith
  have hdt : d * t = (q + C * t) / 2 := by
    dsimp [d]
    field_simp [ht.ne']
  have hqdt : q < d * t := by rw [hdt]; linarith
  let ratio : ℝ := d * t / q
  have hratio : 1 < ratio := by
    dsimp [ratio]
    exact (lt_div_iff₀ hq).2 (by simpa using hqdt)
  have hratioPos : 0 < ratio := lt_trans zero_lt_one hratio
  let b : ℝ := (1 + Real.sqrt ratio) / 2
  have hsqrtOne : 1 < Real.sqrt ratio := by
    have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hratio
    simpa using hs
  have hb : 1 < b := by dsimp [b]; linarith
  have hbsqrt : b < Real.sqrt ratio := by dsimp [b]; linarith
  have hbPos : 0 < b := lt_trans zero_lt_one hb
  have hbSq : b ^ 2 < ratio := by
    have hsqrtPos : 0 < Real.sqrt ratio := Real.sqrt_pos.2 hratioPos
    have hproduct :
        0 < (Real.sqrt ratio - b) * (Real.sqrt ratio + b) :=
      mul_pos (sub_pos.mpr hbsqrt) (add_pos hsqrtPos hbPos)
    have hsquare : (Real.sqrt ratio) ^ 2 = ratio := Real.sq_sqrt hratioPos.le
    nlinarith
  have hbq : b ^ 2 * q < d * t := by
    have hratio' : b ^ 2 < d * t / q := by simpa [ratio] using hbSq
    exact (lt_div_iff₀ hq).1 hratio'
  have hmargin : q < d * t / b ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hbPos)).2
    simpa [mul_comm] using hbq
  let c : ℝ := b / (b + q)
  have hcEq : c = b / (b + a + zeta0) := by
    dsimp [c, q]
    ring
  have hcPos : 0 < c := by
    dsimp [c]
    exact div_pos hbPos (by linarith)
  have hcLt : c < 1 := by
    dsimp [c]
    apply (div_lt_one (by linarith)).2
    linarith
  let margin : ℝ := d * t / b ^ 2 - q
  have hmarginPos : 0 < margin := by dsimp [margin]; linarith
  let epsilon : ℝ := min (b - 1) margin / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilonB : epsilon < b - 1 := by
    dsimp [epsilon]
    have hmin : min (b - 1) margin ≤ b - 1 := min_le_left _ _
    have hminPos : 0 < min (b - 1) margin := lt_min (sub_pos.mpr hb) hmarginPos
    linarith
  have hepsilonMargin : epsilon < margin := by
    dsimp [epsilon]
    have hmin : min (b - 1) margin ≤ margin := min_le_right _ _
    have hminPos : 0 < min (b - 1) margin := lt_min (sub_pos.mpr hb) hmarginPos
    linarith
  refine ⟨b, d, c, epsilon, hb, hd, hdC, ?_, hcPos, hcLt,
    hepsilon, hepsilonB, ?_⟩
  · simpa [c, q, add_assoc] using hcEq
  · simpa [margin, q] using hepsilonMargin

/-- Complete real-parameter choice for the left-tail proof.  The exponent
`epsilon` is strictly below both competing polynomial exponents, so the final
union bound has a positive power margin. -/
theorem exists_leftTailParameters
    {a t C zeta : ℝ} (ht : 0 < t) (hC : 0 < C)
    (hzeta : zeta < -a + C * t) :
    ∃ zeta0 b d c epsilon : ℝ,
      max zeta (-a) < zeta0 ∧ zeta0 < -a + C * t ∧
      1 < b ∧ 0 < d ∧ d < C ∧
      c = b / (b + a + zeta0) ∧ 0 < c ∧ c < 1 ∧
      0 < epsilon ∧ epsilon < b - 1 ∧
      epsilon < d * t / b ^ 2 - (a + zeta0) := by
  obtain ⟨zeta0, hzeta0Lower, hzeta0Upper⟩ :=
    exists_leftTailIntermediateLevel ht hC hzeta
  have hminus : -a < zeta0 := lt_of_le_of_lt (le_max_right _ _) hzeta0Lower
  obtain ⟨b, d, c, epsilon, hb, hd, hdC, hcEq, hcPos, hcLt,
      hepsilon, hepsilonB, hepsilonMargin⟩ :=
    exists_leftTailExponentParameters ht hC hminus hzeta0Upper
  refine ⟨zeta0, b, d, c, epsilon, hzeta0Lower, hzeta0Upper,
    hb, hd, hdC, ?_, hcPos, hcLt, hepsilon, hepsilonB, ?_⟩
  · simpa using hcEq
  · simpa using hepsilonMargin

end ProbabilityTheory.BranchingRandomWalk.Analytic

end
