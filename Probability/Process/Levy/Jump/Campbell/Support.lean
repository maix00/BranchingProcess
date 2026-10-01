import Probability.Process.Levy.Jump.Campbell.Integrability
import Probability.Process.Levy.Jump.Intensity.TimeMark

/-!
# Support of a Poisson random measure

If the intensity is carried by a measurable set, almost every realized
Poisson measure is carried by that same set. This is useful when passing
between a full jump integral and its cutoff-restricted path definition.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- Zero intensity forces zero realized Poisson mass almost surely. -/
theorem IsPoissonPointFamily.ae_poissonRandomMeasure_apply_eq_zero
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {A : Set E} (hA : MeasurableSet A) (hzero : m A = 0) :
    ∀ᵐ ω ∂P, poissonRandomMeasure K X ω A = 0 := by
  apply (lintegral_eq_zero_iff
    (measurable_poissonRandomMeasure_apply hd.measurable_count
      hd.measurable_point hA)).mp
  exact (lintegral_poissonRandomMeasure_apply hd hA).trans hzero

theorem IsPoissonPointFamily.ae_restrict_poissonRandomMeasure_eq_self
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {A : Set E} (hA : MeasurableSet A) (hcarrier : m Aᶜ = 0) :
    ∀ᵐ ω ∂P, (poissonRandomMeasure K X ω).restrict A =
      poissonRandomMeasure K X ω := by
  have hzero := hd.ae_poissonRandomMeasure_apply_eq_zero hA.compl hcarrier
  filter_upwards [hzero] with ω hω
  apply Measure.restrict_eq_self_of_ae_mem
  change A ∈ ae (poissonRandomMeasure K X ω)
  exact mem_ae_iff.mpr hω

/-- A product-intensity Poisson source has no point at a fixed time. -/
theorem IsPoissonPointFamily.ae_no_jump_at_time
    {Ω : Type} [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X
      ((volume : Measure unitInterval).prod ν) P)
    (t : unitInterval) :
    ∀ᵐ ω ∂P,
      poissonRandomMeasure K X ω ({t} ×ˢ Set.univ) = 0 := by
  exact hd.ae_poissonRandomMeasure_apply_eq_zero
    (MeasurableSet.prod (measurableSet_singleton (x := t)) MeasurableSet.univ)
    (unitTime_prod_singleton_time_zero ν t)

/-- If the intensity has no positive values of a real mark observable,
the realized Poisson integral is nonpositive almost surely. -/
theorem IsPoissonPointFamily.ae_integral_nonpos_of_no_positive_intensity
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f)
    (hzero : m {x | 0 < f x} = 0) :
    ∀ᵐ ω ∂P, (∫ x, f x ∂(poissonRandomMeasure K X ω)) ≤ 0 := by
  have hpos := hd.ae_poissonRandomMeasure_apply_eq_zero
    (measurableSet_lt measurable_const hf) hzero
  filter_upwards [hpos] with ω hω
  apply integral_nonpos_of_ae
  have hmem : {x | f x ≤ 0} ∈ ae (poissonRandomMeasure K X ω) := by
    apply mem_ae_iff.mpr
    have hset : ({x | f x ≤ 0} : Set E)ᶜ = {x | 0 < f x} := by
      ext x
      simp
    rwa [hset]
  exact hmem

/-- An intensity with no negative values yields a nonnegative realized
Poisson integral almost surely. -/
theorem IsPoissonPointFamily.ae_integral_nonneg_of_no_negative_intensity
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f)
    (hzero : m {x | f x < 0} = 0) :
    ∀ᵐ ω ∂P, 0 ≤ (∫ x, f x ∂(poissonRandomMeasure K X ω)) := by
  have hneg := hd.ae_poissonRandomMeasure_apply_eq_zero
    (measurableSet_lt hf measurable_const) hzero
  filter_upwards [hneg] with ω hω
  apply integral_nonneg_of_ae
  apply mem_ae_iff.mpr
  have hset : ({x | 0 ≤ f x} : Set E)ᶜ = {x | f x < 0} := by
    ext x
    simp
  change (poissonRandomMeasure K X ω) ({x | 0 ≤ f x} : Set E)ᶜ = 0
  rwa [hset]

end ProbabilityTheory
