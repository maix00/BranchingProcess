/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition

/-!
# Finite products of stable exponential block bounds.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A finite product of exponential block bounds gives the sum of their
limiting logarithmic rates. The error is arbitrary; this is the analytic
step that lets the endpoint-core losses tend to zero in the corridor lower
bound. -/
theorem eventually_probabilityRate_ge_finiteProductRate
    {ι : Type*} [Fintype ι] {rate : ℕ → ℝ}
    {probability : ℕ → ENNReal}
    (exponent : ι → ℝ) (count : ι → ℕ → ℕ)
    (countRate : ι → ℝ)
    (hcount : ∀ i, Tendsto (fun n => rate n * (count i n : ℝ))
      atTop (nhds (countRate i)))
    (hproduct : ∀ᶠ n : ℕ in atTop,
      (∏ i : ι, ENNReal.ofReal (Real.exp (exponent i)) ^ count i n) ≤
        probability n)
    (hrateNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ rate n)
    (hprobabilityLeOne : ∀ n, probability n ≤ 1)
    {error : ℝ} (herror : 0 < error) :
    ∀ᶠ n : ℕ in atTop,
      0 < probability n ∧
        (∑ i : ι, countRate i * exponent i) - error ≤
          rate n * Real.log (probability n).toReal := by
  classical
  let factor (i : ι) (n : ℕ) : ENNReal :=
    ENNReal.ofReal (Real.exp (exponent i)) ^ count i n
  let logarithmicLower (n : ℕ) : ℝ :=
    ∑ i : ι, rate n * (count i n : ℝ) * exponent i
  let limitingLower : ℝ := ∑ i : ι, countRate i * exponent i
  have hterm (i : ι) : Tendsto
      (fun n => rate n * (count i n : ℝ) * exponent i)
      atTop (nhds (countRate i * exponent i)) := by
    exact (hcount i).mul_const (exponent i)
  have hlogarithmicLower : Tendsto logarithmicLower atTop (nhds limitingLower) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset ι)
      (fun i _ => hterm i)
    simpa [logarithmicLower, limitingLower] using hsum
  have hlogProductLe : ∀ᶠ n : ℕ in atTop,
      Real.log (∏ i : ι, factor i n).toReal ≤
        Real.log (probability n).toReal := by
    filter_upwards [hproduct] with n hproductN
    have hfactorPos (i : ι) : 0 < factor i n := by
      dsimp [factor]
      exact (ENNReal.pow_pos
        (ENNReal.ofReal_pos.mpr (Real.exp_pos (exponent i))) _)
    have hproductPos : 0 < ∏ i : ι, factor i n := by
      apply pos_iff_ne_zero.mpr
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact (hfactorPos i).ne'
    have hprobabilityPos : 0 < probability n :=
      lt_of_lt_of_le hproductPos hproductN
    have hproductTop : (∏ i : ι, factor i n) ≠ ⊤ := by
      have hbound : (∏ i : ι, factor i n) ≤ 1 :=
        hproductN.trans (hprobabilityLeOne n)
      exact ne_of_lt (hbound.trans_lt ENNReal.one_lt_top)
    have hprobabilityTop : probability n ≠ ⊤ :=
      ne_of_lt ((hprobabilityLeOne n).trans_lt ENNReal.one_lt_top)
    have hrealLe : (∏ i : ι, factor i n).toReal ≤ (probability n).toReal :=
      (ENNReal.toReal_le_toReal hproductTop hprobabilityTop).2 hproductN
    have hrealPos : 0 < (∏ i : ι, factor i n).toReal :=
      ENNReal.toReal_pos hproductPos.ne' hproductTop
    exact Real.log_le_log hrealPos hrealLe
  have hfactorPos (i : ι) (n : ℕ) : 0 < (factor i n).toReal := by
    dsimp [factor]
    have hbase : 0 < ENNReal.ofReal (Real.exp (exponent i)) :=
      ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    have hbaseTop : ENNReal.ofReal (Real.exp (exponent i)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    exact ENNReal.toReal_pos (ENNReal.pow_pos hbase _).ne'
      (ENNReal.pow_ne_top hbaseTop)
  have hlogProduct (n : ℕ) :
      Real.log (∏ i : ι, factor i n).toReal =
        ∑ i : ι, (count i n : ℝ) * exponent i := by
    rw [ENNReal.toReal_prod]
    rw [Real.log_prod (fun i _ => (hfactorPos i n).ne')]
    apply Finset.sum_congr rfl
    intro i hi
    have hfactor : (factor i n).toReal =
        Real.exp (exponent i) ^ count i n := by
      dsimp [factor]
      simp [ENNReal.toReal_pow, ENNReal.toReal_ofReal, Real.exp_nonneg]
    rw [hfactor, Real.log_pow, Real.log_exp]
  have hlogarithmicIdentity (n : ℕ) :
      logarithmicLower n =
        rate n * Real.log (∏ i : ι, factor i n).toReal := by
    rw [hlogProduct]
    dsimp [logarithmicLower]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hrateLogLower : ∀ᶠ n : ℕ in atTop,
      logarithmicLower n ≤ rate n * Real.log (probability n).toReal := by
    filter_upwards [hlogProductLe, hrateNonneg] with n hlog hrate
    rw [hlogarithmicIdentity]
    exact mul_le_mul_of_nonneg_left hlog hrate
  have hnear : ∀ᶠ n : ℕ in atTop,
      limitingLower - error < logarithmicLower n := by
    have hlt : limitingLower - error < limitingLower := by linarith
    have hmem := hlogarithmicLower.eventually (isOpen_Ioi.mem_nhds hlt)
    simpa only [Set.mem_Ioi] using hmem
  filter_upwards [hproduct, hnear, hrateLogLower] with n hproductN hnearN hrateN
  have hfactorPos' (i : ι) : 0 < factor i n := by
    dsimp [factor]
    exact (ENNReal.pow_pos
      (ENNReal.ofReal_pos.mpr (Real.exp_pos (exponent i))) _)
  have hproductPos : 0 < ∏ i : ι, factor i n := by
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (hfactorPos' i).ne'
  exact ⟨lt_of_lt_of_le hproductPos hproductN,
    le_of_lt hnearN |>.trans hrateN⟩


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
