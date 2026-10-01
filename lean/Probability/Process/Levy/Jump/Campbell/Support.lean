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

end ProbabilityTheory
