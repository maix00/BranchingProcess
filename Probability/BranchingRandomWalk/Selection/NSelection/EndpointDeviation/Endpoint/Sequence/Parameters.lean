/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-!
# Real parameters for the polynomial endpoint sublevel estimate

These choices are the deterministic parameter step in the proof of (4.16).
The target level is compared directly with the diffusive rate; the endpoint
cutoff is chosen independently and can be made small for every real target.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

/-- Choose the small endpoint ratio used to compare the target height with the
positive endpoint window of the random-walk drawdown estimate. -/
private theorem exists_small_positive_ratio (b r : ℝ) (hb : 0 < b) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧ r < b / c := by
  let c : ℝ := min (1 / 4) (b / (2 * (max r 0 + 1)))
  have hdenom : 0 < 2 * (max r 0 + 1) := by positivity
  have hcpos : 0 < c := by
    dsimp [c]
    apply lt_min
    · norm_num
    · exact div_pos hb hdenom
  have hcsmall : c ≤ b / (2 * (max r 0 + 1)) := by
    dsimp [c]
    exact min_le_right _ _
  have hchalf : c < 1 / 2 := by
    dsimp [c]
    have hcle : min (1 / 4) (b / (2 * (max r 0 + 1))) ≤ 1 / 4 :=
      min_le_left _ _
    norm_num at hcle ⊢
  by_cases hr : r ≤ 0
  · exact ⟨c, hcpos, hchalf, by
      have hbc : 0 < b / c := div_pos hb hcpos
      linarith⟩
  · have hrpos : 0 < r := lt_of_not_ge hr
    have hcoeff : 0 < 2 * (r + 1) := by positivity
    have hcBound : c * (2 * (r + 1)) ≤ b := by
      have hc' : c ≤ b / (2 * (r + 1)) := by
        simpa [max_eq_left hrpos.le] using hcsmall
      exact (le_div_iff₀ hcoeff).mp hc'
    have hprod : r * c < b := by
      calc
        r * c < (2 * (r + 1)) * c :=
          mul_lt_mul_of_pos_right (by nlinarith) hcpos
        _ = c * (2 * (r + 1)) := by ring
        _ ≤ b := hcBound
    exact ⟨c, hcpos, hchalf, (lt_div_iff₀ hcpos).2 hprod⟩

/-- Given a target strictly below the diffusive rate, choose the corridor
parameters used in (4.16). The exponent margin is positive even when the
target lies below `-a`; the small ratio `c` is chosen independently. -/
theorem exists_endpoint_deviation_parameters
    {a t C zeta : ℝ} (ht : 0 < t) (hC : 0 < C)
    (hzeta : zeta < -a + C * t) :
    ∃ b d c epsilon : ℝ,
      1 < b ∧ 0 < d ∧ d < C ∧
      0 < c ∧ c < 1 / 2 ∧ b + a + zeta < b / c ∧
      0 < epsilon ∧ epsilon < b - 1 ∧
      epsilon < d * t / b ^ 2 - (a + zeta) := by
  have hparams : ∃ b d epsilon : ℝ,
      1 < b ∧ 0 < d ∧ d < C ∧
      0 < epsilon ∧ epsilon < b - 1 ∧
      epsilon < d * t / b ^ 2 - (a + zeta) := by
    by_cases hq : 0 < a + zeta
    · let q : ℝ := a + zeta
      have hqpos : 0 < q := by dsimp [q]; exact hq
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
        exact (lt_div_iff₀ hqpos).2 (by simpa using hqdt)
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
        exact (lt_div_iff₀ hqpos).1 hratio'
      have hmargin : 0 < d * t / b ^ 2 - q := by
        apply sub_pos.mpr
        apply (lt_div_iff₀ (sq_pos_of_pos hbPos)).2
        simpa [mul_comm] using hbq
      let epsilon : ℝ := min (b - 1) (d * t / b ^ 2 - q) / 2
      have hepsilon : 0 < epsilon := by
        dsimp [epsilon]
        positivity
      have hepsilonB : epsilon < b - 1 := by
        dsimp [epsilon]
        have hmin : min (b - 1) (d * t / b ^ 2 - q) ≤ b - 1 := min_le_left _ _
        linarith
      have hepsilonMargin : epsilon < d * t / b ^ 2 - q := by
        dsimp [epsilon]
        have hmin : min (b - 1) (d * t / b ^ 2 - q) ≤ d * t / b ^ 2 - q :=
          min_le_right _ _
        linarith
      refine ⟨b, d, epsilon, hb, hd, hdC, hepsilon, hepsilonB, ?_⟩
      simpa [q] using hepsilonMargin
    · let b : ℝ := 2
      let d : ℝ := C / 2
      have hb : 1 < b := by norm_num [b]
      have hd : 0 < d := by dsimp [d]; positivity
      have hdC : d < C := by dsimp [d]; linarith
      have hmargin : 0 < d * t / b ^ 2 - (a + zeta) := by
        have hdtb : 0 < d * t / b ^ 2 :=
          div_pos (mul_pos hd ht) (sq_pos_of_pos (by norm_num [b]))
        linarith
      let epsilon : ℝ := min (b - 1) (d * t / b ^ 2 - (a + zeta)) / 2
      have hepsilon : 0 < epsilon := by
        dsimp [epsilon]
        positivity
      have hepsilonB : epsilon < b - 1 := by
        dsimp [epsilon]
        have hmin : min (b - 1) (d * t / b ^ 2 - (a + zeta)) ≤ b - 1 :=
          min_le_left _ _
        linarith
      have hepsilonMargin : epsilon < d * t / b ^ 2 - (a + zeta) := by
        dsimp [epsilon]
        have hmin : min (b - 1) (d * t / b ^ 2 - (a + zeta)) ≤
            d * t / b ^ 2 - (a + zeta) := min_le_right _ _
        linarith
      exact ⟨b, d, epsilon, hb, hd, hdC, hepsilon, hepsilonB, hepsilonMargin⟩
  obtain ⟨b, d, epsilon, hb, hd, hdC, hepsilon, hepsilonB, hepsilonMargin⟩ := hparams
  obtain ⟨c, hc, hcHalf, hcEndpoint⟩ :=
    exists_small_positive_ratio b (b + a + zeta) (by linarith)
  exact ⟨b, d, c, epsilon, hb, hd, hdC, hc, hcHalf, hcEndpoint,
    hepsilon, hepsilonB, hepsilonMargin⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

end
