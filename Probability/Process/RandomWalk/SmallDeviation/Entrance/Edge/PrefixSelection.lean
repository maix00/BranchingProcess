/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.BoundedWindows
public import Analysis.Asymptotics.ShiftedFloor

/-!
# Fixed entrance prefixes for the two edge intervals

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_positive_mass_prefixes`:
  for a centered law with variance $\sigma^2>0$ and $c\ge0$, there are
  fixed positive and negative increment windows $[a_+,b_+]$ and
  $[a_-,b_-]$ of positive probability, and fixed prefix lengths
  $m_+,m_-$ with $m_+a_+>c+1$ and $m_-a_->c+1$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.eventually_prefix_geometry`:
  for widths $\Delta\to\infty$, every fixed choice of prefix lengths and
  positive increment windows eventually satisfies the width and horizon
  inequalities used by the two edge inclusions.

This is the finite-prefix selection in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma used in Chapter 3,
Lemma 3.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- Positive-mass increment windows and fixed prefix lengths on both edges
of the entrance corridor. -/
theorem exists_positive_mass_prefixes
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (drift : ℝ) :
    ∃ aPlus bPlus aMinus bMinus : ℝ, ∃ mPlus mMinus : ℕ,
      0 < aPlus ∧ aPlus < bPlus ∧
      0 < ν (Set.Icc aPlus bPlus) ∧
      0 < aMinus ∧ aMinus < bMinus ∧
      0 < (ν.map fun x : ℝ => -x) (Set.Icc aMinus bMinus) ∧
      drift + 1 < (mPlus : ℝ) * aPlus ∧
      drift + 1 < (mMinus : ℝ) * aMinus := by
  obtain ⟨aPlus, bPlus, haPlus, habPlus, hpPlus⟩ :=
    hν.exists_pos_Icc_measure_pos hsigma
  obtain ⟨aMinus, bMinus, haMinus, habMinus, hpMinus⟩ :=
    hν.exists_reflected_pos_Icc_measure_pos hsigma
  obtain ⟨mPlus, hmPlus⟩ := exists_nat_gt ((drift + 1) / aPlus)
  obtain ⟨mMinus, hmMinus⟩ := exists_nat_gt ((drift + 1) / aMinus)
  refine ⟨aPlus, bPlus, aMinus, bMinus, mPlus, mMinus,
    haPlus, habPlus, hpPlus, haMinus, habMinus, hpMinus, ?_, ?_⟩
  · exact (div_lt_iff₀ haPlus).mp hmPlus
  · exact (div_lt_iff₀ haMinus).mp hmMinus

/-- The fixed prefix lengths and bounded increment windows fit into a
diffusive corridor as its width tends to infinity. -/
theorem eventually_prefix_geometry
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift aPlus bPlus bMinus : ℝ}
    (haPlus : 0 < aPlus) (mPlus mMinus : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      0 < width n ∧
      12 * drift ≤ width n ∧
      12 * (mPlus : ℝ) * bPlus ≤ width n ∧
      24 * (mMinus : ℝ) * bMinus ≤ width n ∧
      24 * drift ≤ width n ∧
      drift ≤ aPlus * width n ^ 2 ∧
      mPlus ≤ Asymptotics.floorBlockLength (fun k => width k ^ 2) n ∧
      mMinus ≤ Asymptotics.floorBlockLength (fun k => width k ^ 2) n := by
  have hsq : Tendsto (fun n => width n ^ 2) atTop atTop := by
    have hmul := hwidth.atTop_mul_atTop₀ hwidth
    simpa [pow_two] using hmul
  have hlength : Tendsto
      (Asymptotics.floorBlockLength (fun k => width k ^ 2))
      atTop atTop :=
    Asymptotics.tendsto_floorBlockLength_atTop hsq
  have hlarge := hwidth.eventually
    (eventually_ge_atTop
      (max 1 (max (24 * drift)
        (max (12 * (mPlus : ℝ) * bPlus)
          (max (24 * (mMinus : ℝ) * bMinus) (drift / aPlus))))))
  have hplus := hlength.eventually (eventually_ge_atTop mPlus)
  have hminus := hlength.eventually (eventually_ge_atTop mMinus)
  filter_upwards [hlarge, hplus, hminus] with n hn hnp hnm
  have hwone : 1 ≤ width n := (le_max_left _ _).trans hn
  have hwd : 24 * drift ≤ width n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hwp : 12 * (mPlus : ℝ) * bPlus ≤ width n := by
    calc
      12 * (mPlus : ℝ) * bPlus ≤
          max (12 * (mPlus : ℝ) * bPlus)
            (max (24 * (mMinus : ℝ) * bMinus) (drift / aPlus)) :=
        le_max_left _ _
      _ ≤ width n :=
        (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hwm : 24 * (mMinus : ℝ) * bMinus ≤ width n := by
    calc
      24 * (mMinus : ℝ) * bMinus ≤
          max (24 * (mMinus : ℝ) * bMinus) (drift / aPlus) :=
        le_max_left _ _
      _ ≤ width n :=
        (le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hratio : drift / aPlus ≤ width n := by
    calc
      drift / aPlus ≤
          max (24 * (mMinus : ℝ) * bMinus) (drift / aPlus) :=
        le_max_right _ _
      _ ≤ width n :=
        (le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hstep : drift ≤ aPlus * width n ^ 2 := by
    have hlinear : drift ≤ aPlus * width n :=
      by simpa [mul_comm] using (div_le_iff₀ haPlus).mp hratio
    have hsqbound : width n ≤ width n ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsqbound haPlus.le]
  have h12 : 12 * drift ≤ width n := by
    by_cases hd : 0 ≤ drift <;> linarith
  exact ⟨by linarith, h12, hwp, hwm, hwd, hstep, hnp, hnm⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
