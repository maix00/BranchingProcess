import Probability.Distributions.Moments.Real
import Mathlib.MeasureTheory.Measure.Support

/-!
# Two-sided increments under centered second-moment assumptions

A centered increment law with nonzero second moment must charge both open
half-lines.  These facts are the measure-theoretic input for constructing a
subexponential entrance path from either boundary of a corridor.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

/-- A centered unit-second-moment law assigns positive mass to negative
increments. -/
theorem IsCenteredUnitSecondMoment.measure_Iio_zero_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    0 < ν (Iio 0) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hnonneg : ∀ᵐ x : ℝ ∂ν, 0 ≤ x := by
    apply (ae_iff).2
    have hset : {x : ℝ | ¬0 ≤ x} = Iio 0 := by
      ext x
      simp
    rw [hset]
    exact hzero
  have hintegrable : Integrable (fun x : ℝ => x) ν := by
    change Integrable id ν
    exact hν.memLp_two.integrable (by norm_num)
  have hzeroAe : (fun x : ℝ => x) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hintegrable).1 hν.1
  have hsquareZero : (fun x : ℝ => x ^ 2) =ᵐ[ν] 0 :=
    hzeroAe.mono fun x hx => by simp [hx]
  have hsquareIntegral : (∫ x : ℝ, x ^ 2 ∂ν) = 0 :=
    integral_eq_zero_of_ae hsquareZero
  linarith [hν.2]

/-- A centered unit-second-moment law assigns positive mass to positive
increments. -/
theorem IsCenteredUnitSecondMoment.measure_Ioi_zero_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    0 < ν (Ioi 0) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hnonpos : ∀ᵐ x : ℝ ∂ν, x ≤ 0 := by
    apply (ae_iff).2
    have hset : {x : ℝ | ¬x ≤ 0} = Ioi 0 := by
      ext x
      simp
    rw [hset]
    exact hzero
  have hintegrable : Integrable (fun x : ℝ => -x) ν := by
    change Integrable (-id) ν
    exact (hν.memLp_two.integrable (by norm_num)).neg
  have hnonneg : ∀ᵐ x : ℝ ∂ν, 0 ≤ -x :=
    hnonpos.mono fun _ hx => neg_nonneg.mpr hx
  have hintegral : (∫ x : ℝ, -x ∂ν) = 0 := by
    rw [integral_neg, hν.1, neg_zero]
  have hzeroAe : (fun x : ℝ => -x) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hintegrable).1 hintegral
  have hsquareZero : (fun x : ℝ => x ^ 2) =ᵐ[ν] 0 :=
    hzeroAe.mono fun x hx => by
      have : x = 0 := neg_eq_zero.mp hx
      simp [this]
  have hsquareIntegral : (∫ x : ℝ, x ^ 2 ∂ν) = 0 :=
    integral_eq_zero_of_ae hsquareZero
  linarith [hν.2]

/-- Some bounded open interval of strictly negative increments has positive
mass.  In particular, the increments in this event are bounded away from
both zero and minus infinity. -/
theorem IsCenteredUnitSecondMoment.exists_neg_interval_measure_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    ∃ lower upper : ℝ,
      lower < upper ∧ upper < 0 ∧ 0 < ν (Ioo lower upper) := by
  obtain ⟨x, hx, hxsupport⟩ :=
    ν.nonempty_inter_support_of_pos hν.measure_Iio_zero_pos
  have hxneg : x < 0 := hx
  let radius := -x / 2
  have hradius : 0 < radius := by dsimp [radius]; linarith
  refine ⟨x - radius, x + radius, by linarith, ?_, ?_⟩
  · dsimp [radius]
    linarith
  · apply (Measure.mem_support_iff_forall x).1 hxsupport
    exact Ioo_mem_nhds (by linarith) (by linarith)

/-- Some bounded open interval of strictly positive increments has positive
mass. -/
theorem IsCenteredUnitSecondMoment.exists_pos_interval_measure_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    ∃ lower upper : ℝ,
      0 < lower ∧ lower < upper ∧ 0 < ν (Ioo lower upper) := by
  obtain ⟨x, hx, hxsupport⟩ :=
    ν.nonempty_inter_support_of_pos hν.measure_Ioi_zero_pos
  have hxpos : 0 < x := hx
  let radius := x / 2
  have hradius : 0 < radius := by dsimp [radius]; linarith
  refine ⟨x - radius, x + radius, ?_, by linarith, ?_⟩
  · dsimp [radius]
    linarith
  · apply (Measure.mem_support_iff_forall x).1 hxsupport
    exact Ioo_mem_nhds (by linarith) (by linarith)

end ProbabilityTheory.RandomWalk
