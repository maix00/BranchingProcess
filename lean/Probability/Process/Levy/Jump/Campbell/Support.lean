import Probability.Process.Levy.Jump.Campbell.Integrability

/-!
# Support of a Poisson random measure

If the intensity is carried by a measurable set, almost every realized
Poisson measure is carried by that same set. This is useful when passing
between a full jump integral and its cutoff-restricted path definition.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem IsPoissonPointFamily.ae_restrict_poissonRandomMeasure_eq_self
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {A : Set E} (hA : MeasurableSet A) (hcarrier : m Aᶜ = 0) :
    ∀ᵐ ω ∂P, (poissonRandomMeasure K X ω).restrict A =
      poissonRandomMeasure K X ω := by
  have hzero : ∀ᵐ ω ∂P, poissonRandomMeasure K X ω Aᶜ = 0 := by
    apply (lintegral_eq_zero_iff
      (measurable_poissonRandomMeasure_apply hd.measurable_count
        hd.measurable_point hA.compl)).mp
    exact (lintegral_poissonRandomMeasure_apply hd hA.compl).trans hcarrier
  filter_upwards [hzero] with ω hω
  apply Measure.restrict_eq_self_of_ae_mem
  change A ∈ ae (poissonRandomMeasure K X ω)
  exact mem_ae_iff.mpr hω

end ProbabilityTheory
