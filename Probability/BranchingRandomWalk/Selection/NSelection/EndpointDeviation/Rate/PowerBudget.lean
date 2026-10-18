module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

/-!
# Polynomial power budgets

Elementary asymptotic bookkeeping for converting a one-root power lower
bound into a growing number of successful roots.  This is the exponent step
used after a Paley--Zygmund estimate in the positive-initial-mass argument.
-/

open Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open scoped ENNReal

/-- A polynomial lower bound for the one-root success probability gives a
polynomial lower bound for the expected number of successful roots. -/
theorem eventually_floorPower_mul_power_ge
    {a r δ : ℝ} (ha : 0 < a) (hgap : δ < a + r) :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.floor ((n : ℝ) ^ a) : ℕ) : ℝ) * (n : ℝ) ^ r / 4 ≥
        (n : ℝ) ^ δ := by
  let gap : ℝ := a + r - δ
  have hgapPos : 0 < gap := by dsimp [gap]; linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (_root_.tendsto_rpow_atTop ha).comp hnat
  have hfloor : Tendsto
      (fun n : ℕ => (Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp harg
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ gap) atTop atTop :=
    (_root_.tendsto_rpow_atTop hgapPos).comp hnat
  filter_upwards [
    hfloor.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hpower.eventually_gt_atTop 8,
    hnat.eventually_ge_atTop 1] with n hfloor hpower hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hargPos : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hnpos _
  have hratio :
      (1 / 2 : ℝ) < (Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a := hfloor
  have hratioPos : 0 <
      (Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a := by linarith
  have hpowPos : 0 < (n : ℝ) ^ gap := Real.rpow_pos_of_pos hnpos _
  have hmul : 4 <
      ((Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a) * (n : ℝ) ^ gap := by
    calc
      4 = (1 / 2 : ℝ) * 8 := by norm_num
      _ < ((Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a) * 8 :=
        mul_lt_mul_of_pos_right hratio (by norm_num)
      _ < ((Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a) *
          (n : ℝ) ^ gap := mul_lt_mul_of_pos_left hpower hratioPos
  have hscale :
      ((Nat.floor ((n : ℝ) ^ a) : ℝ) * (n : ℝ) ^ r / 4) /
          (n : ℝ) ^ δ =
        ((Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a) *
          (n : ℝ) ^ gap / 4 := by
    have hquot : (n : ℝ) ^ r / (n : ℝ) ^ δ = (n : ℝ) ^ (r - δ) :=
      (Real.rpow_sub hnpos r δ).symm
    have hgapquot : (n : ℝ) ^ gap / (n : ℝ) ^ a =
        (n : ℝ) ^ (gap - a) := (Real.rpow_sub hnpos gap a).symm
    have hexp : r - δ = gap - a := by dsimp [gap]; ring
    calc
      ((Nat.floor ((n : ℝ) ^ a) : ℝ) * (n : ℝ) ^ r / 4) /
          (n : ℝ) ^ δ =
        ((Nat.floor ((n : ℝ) ^ a) : ℝ) *
          ((n : ℝ) ^ r / (n : ℝ) ^ δ)) / 4 := by ring
      _ = ((Nat.floor ((n : ℝ) ^ a) : ℝ) * (n : ℝ) ^ (r - δ)) / 4 := by
        rw [hquot]
      _ = ((Nat.floor ((n : ℝ) ^ a) : ℝ) * (n : ℝ) ^ (gap - a)) / 4 := by
        rw [hexp]
      _ = ((Nat.floor ((n : ℝ) ^ a) : ℝ) *
          ((n : ℝ) ^ gap / (n : ℝ) ^ a)) / 4 := by
        rw [hgapquot]
      _ = ((Nat.floor ((n : ℝ) ^ a) : ℝ) / (n : ℝ) ^ a) *
          (n : ℝ) ^ gap / 4 := by ring
  have hratioGreat : 1 <
      ((Nat.floor ((n : ℝ) ^ a) : ℝ) * (n : ℝ) ^ r / 4) /
        (n : ℝ) ^ δ := by
    rw [hscale]
    nlinarith
  have hdeltaPos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hnpos _
  have hresult : 1 * (n : ℝ) ^ δ <
      (Nat.floor ((n : ℝ) ^ a) : ℝ) * (n : ℝ) ^ r / 4 :=
    (lt_div_iff₀ hdeltaPos).mp hratioGreat
  have hresult' : (n : ℝ) ^ δ <
      (Nat.floor ((n : ℝ) ^ a) : ℝ) * (n : ℝ) ^ r / 4 := by
    simpa only [one_mul] using hresult
  exact hresult'.le

/-- The lower-tail threshold in the independent-root estimate exceeds
`n^δ` once the one-root PZ probability has the polynomial lower
rate.  The analytic hypothesis is exactly the output needed from the
first-stage one-root tube estimate. -/
theorem eventually_floorPower_mul_ennreal_toReal_ge
    {a r δ : ℝ} (ha : 0 < a) (hgap : δ < a + r)
    (p : ℕ → ℝ≥0∞)
    (hp : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ r ≤ (p n).toReal) :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.floor ((n : ℝ) ^ a) : ℕ) : ℝ) * (p n).toReal / 4 ≥
        (n : ℝ) ^ δ := by
  have hbase := eventually_floorPower_mul_power_ge ha hgap
  filter_upwards [hbase, hp, (tendsto_natCast_atTop_atTop.eventually_ge_atTop 1)]
    with n hbase hp hn
  have hfloorNonneg :
      0 ≤ ((Nat.floor ((n : ℝ) ^ a) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmonotone := mul_le_mul_of_nonneg_left hp hfloorNonneg
  have hmonotone' := div_le_div_of_nonneg_right hmonotone (by norm_num : (0:ℝ) ≤ 4)
  exact le_trans hbase hmonotone'

/-- The same power budget with an arbitrary sample-size sequence tending to
infinity. This is the form used when the particle count is
`floor ((N n : ℝ) ^ a)`. -/
theorem eventually_floorPowerOfSampleSize_mul_ennreal_toReal_ge
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {a r δ : ℝ} (ha : 0 < a) (hgap : δ < a + r)
    (p : ℕ → ℝ≥0∞)
    (hp : ∀ᶠ n : ℕ in atTop,
      (N n : ℝ) ^ r ≤ (p n).toReal) :
    ∀ᶠ n : ℕ in atTop,
      ((Nat.floor ((N n : ℝ) ^ a) : ℕ) : ℝ) * (p n).toReal / 4 ≥
        (N n : ℝ) ^ δ := by
  have hbase := eventually_floorPower_mul_power_ge ha hgap
  have hbaseN : ∀ᶠ n : ℕ in atTop,
      ((Nat.floor ((N n : ℝ) ^ a) : ℕ) : ℝ) * (N n : ℝ) ^ r / 4 ≥
        (N n : ℝ) ^ δ := hN.eventually hbase
  filter_upwards [hbaseN, hp, hN.eventually_gt_atTop 0] with n hbase hp hNpos
  have hfloorNonneg :
      0 ≤ ((Nat.floor ((N n : ℝ) ^ a) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmonotone := mul_le_mul_of_nonneg_left hp hfloorNonneg
  have hmonotone' := div_le_div_of_nonneg_right hmonotone
    (by norm_num : (0 : ℝ) ≤ 4)
  exact le_trans hbase hmonotone'

/-- Moment power bounds pass through Paley--Zygmund with the expected
exponent: a first-moment lower rate `N^α` and second-moment upper rate
`N^β` give a one-root success lower rate `N^(2α-β)`. -/
theorem ennreal_sq_div_toReal_ge_of_power_bounds
    {x y : ℝ≥0∞} {N α β : ℝ}
    (hN : 0 < N) (hyTop : y ≠ ∞) (hyPos : 0 < y)
    (hx : N ^ α ≤ x.toReal) (hy : y.toReal ≤ N ^ β) :
    N ^ (2 * α - β) ≤ (x ^ 2 / y).toReal := by
  have hyRealPos : 0 < y.toReal :=
    ENNReal.toReal_pos (ne_of_gt hyPos) hyTop
  have hpow : N ^ (2 * α) ≤ x.toReal ^ 2 := by
    have hexp : N ^ (2 * α) = (N ^ α) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
      congr 1
      ring
    rw [hexp]
    have hbaseNonneg : 0 ≤ N ^ α := Real.rpow_nonneg hN.le _
    have hxNonneg : 0 ≤ x.toReal := ENNReal.toReal_nonneg
    nlinarith [sq_nonneg (x.toReal - N ^ α)]
  have hmul : N ^ (2 * α - β) * y.toReal ≤ x.toReal ^ 2 := by
    calc
      N ^ (2 * α - β) * y.toReal ≤ N ^ (2 * α - β) * N ^ β :=
        mul_le_mul_of_nonneg_left hy (Real.rpow_nonneg hN.le _)
      _ = N ^ (2 * α) := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ x.toReal ^ 2 := hpow
  have hquot : N ^ (2 * α - β) ≤ x.toReal ^ 2 / y.toReal :=
    (le_div_iff₀ hyRealPos).2 hmul
  simpa [ENNReal.toReal_div, ENNReal.toReal_pow] using hquot

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
