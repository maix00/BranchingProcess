/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithms of finite products of probabilities

This file collects the elementary conversion from an ENNReal probability
product bound to a real logarithmic sum. It is useful when independent-event
factorization supplies the product estimate and the event being bounded has
positive probability.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- If a positive event probability is bounded by a finite product of event
probabilities, its real logarithm is bounded by the sum of their real
logarithms. -/
theorem measure_log_toReal_le_sum_log_toReal_of_le_finsetProduct
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} (s : Finset ι) (G : Set Ω) (E : ι → Set Ω)
    (hbound : P G ≤ ∏ i ∈ s, P (E i))
    (hpositive : 0 < (P G).toReal) :
    Real.log ((P G).toReal) ≤
      ∑ i ∈ s, Real.log ((P (E i)).toReal) := by
  have hGpos : 0 < P G := (ENNReal.toReal_pos_iff.mp hpositive).1
  have hproductPos : 0 < ∏ i ∈ s, P (E i) := lt_of_lt_of_le hGpos hbound
  have hproductNeZero : ∏ i ∈ s, P (E i) ≠ 0 :=
    pos_iff_ne_zero.mp hproductPos
  have hfactorPos : ∀ i ∈ s, 0 < P (E i) := by
    intro i hi
    exact pos_iff_ne_zero.mpr
      ((Finset.prod_ne_zero_iff.mp hproductNeZero) i hi)
  have hproductNeTop : ∏ i ∈ s, P (E i) ≠ ⊤ := ENNReal.prod_ne_top (by
    intro i hi
    exact (measure_lt_top P (E i)).ne)
  have hreal := ENNReal.toReal_mono hproductNeTop hbound
  have hlog := Real.log_le_log hpositive hreal
  have hlogProduct : Real.log ((∏ i ∈ s, P (E i)).toReal) =
      ∑ i ∈ s, Real.log ((P (E i)).toReal) := by
    rw [ENNReal.toReal_prod]
    exact Real.log_prod (fun i hi =>
      (ENNReal.toReal_pos_iff.mpr
        ⟨hfactorPos i hi, measure_lt_top P (E i)⟩).ne')
  rw [hlogProduct] at hlog
  exact hlog

/-- If a finite product of event probabilities is bounded above by a target
probability and the product is positive, its real logarithm is bounded above
by the target logarithm. -/
theorem sum_log_toReal_le_measure_log_toReal_of_finsetProduct_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} (s : Finset ι) (G : Set Ω) (E : ι → Set Ω)
    (hbound : ∏ i ∈ s, P (E i) ≤ P G)
    (hpositive : 0 < ∏ i ∈ s, P (E i)) :
    ∑ i ∈ s, Real.log ((P (E i)).toReal) ≤ Real.log ((P G).toReal) := by
  have hfactorPos : ∀ i ∈ s, 0 < P (E i) := by
    intro i hi
    exact pos_iff_ne_zero.mpr
      ((Finset.prod_ne_zero_iff.mp (pos_iff_ne_zero.mp hpositive)) i hi)
  have hproductNeTop : ∏ i ∈ s, P (E i) ≠ ⊤ := ENNReal.prod_ne_top (by
    intro i hi
    exact (measure_lt_top P (E i)).ne)
  have hproductToRealPos : 0 < (∏ i ∈ s, P (E i)).toReal :=
    (ENNReal.toReal_pos_iff.mpr ⟨hpositive, hproductNeTop.lt_top⟩)
  have hreal : (∏ i ∈ s, P (E i)).toReal ≤ (P G).toReal :=
    ENNReal.toReal_mono (measure_lt_top P G).ne hbound
  have hlog := Real.log_le_log hproductToRealPos hreal
  have hlogProduct : Real.log ((∏ i ∈ s, P (E i)).toReal) =
      ∑ i ∈ s, Real.log ((P (E i)).toReal) := by
    rw [ENNReal.toReal_prod]
    exact Real.log_prod (fun i hi =>
      (ENNReal.toReal_pos_iff.mpr
        ⟨hfactorPos i hi, measure_lt_top P (E i)⟩).ne')
  rw [hlogProduct] at hlog
  exact hlog

end ProbabilityTheory

end
