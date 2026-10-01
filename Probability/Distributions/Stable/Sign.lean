module

public import Probability.Distributions.Stable.Basic
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Signs in a stable law

The original small-deviation hypothesis is stated using the cumulative
distribution function at zero. With an atomless law, it is equivalent to
positive mass on each open half-line. This file uses Mathlib's `cdf`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- Under atomlessness, the original condition `0 < F(0) < 1` gives
positive mass to both signs. -/
theorem IsStrictlyAlphaStable.twoSidedMass_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    [NullSingletonClass μ]
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < μ (Set.Iio 0) ∧ 0 < μ (Set.Ioi 0) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hIic : μ (Set.Iic 0) = ENNReal.ofReal (cdf μ 0) :=
    (ofReal_cdf μ 0).symm
  have hIio : μ (Set.Iio 0) = μ (Set.Iic 0) :=
    measure_congr (Iio_ae_eq_Iic : Set.Iio (0 : ℝ) =ᵐ[μ] Set.Iic 0)
  constructor
  · rw [hIio, hIic]
    exact ENNReal.ofReal_pos.mpr hcdf.1
  · have hlt : μ (Set.Iic 0) < 1 := by
      rw [hIic]
      exact ENNReal.ofReal_lt_one.mpr hcdf.2
    have hcompl : μ (Set.Ioi 0) = 1 - μ (Set.Iic 0) := by
      rw [← Set.compl_Iic, measure_compl measurableSet_Iic (by finiteness)]
      simp
    rw [hcompl]
    exact tsub_pos_iff_lt.mpr hlt

end ProbabilityTheory

end
