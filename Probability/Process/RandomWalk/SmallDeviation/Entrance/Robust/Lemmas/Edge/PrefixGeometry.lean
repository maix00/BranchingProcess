/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.ShiftedFloor

/-!
# Width conditions for fixed entrance prefixes

The supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.eventually_prefix_geometry`:
  for widths $\Delta_n\to\infty$, fixed prefix lengths $m_+,m_-$ and
  fixed positive increment windows, the width, drift, and diffusive-horizon
  inequalities used by the two edge inclusions hold eventually.

This is the finite-prefix geometry step in Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Appendix A.2, Lemma A.7, used in Chapter 3, Lemma 3.5.
-/

@[expose] public section

open Filter

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The fixed prefix lengths and bounded increment windows fit into a
diffusive corridor as its width tends to infinity. -/
lemma eventually_prefix_geometry
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
