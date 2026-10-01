import Probability.Process.Levy.Jump.Campbell

/-!
# Almost-sure integrability of Poisson jump sums

Campbell's identity turns a finite intensity integral of a nonnegative
weight into almost-sure finiteness of its realized Poisson integral. This
is used for the small-jump part of a finite-variation Lévy process; large
jumps instead have finite count and need no global first moment.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem IsPoissonPointFamily.ae_lintegral_poissonRandomMeasure_lt_top
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {g : E → ENNReal} (hg : Measurable g)
    (hfinite : (∫⁻ x, g x ∂m) < ⊤) :
    ∀ᵐ ω ∂P, (∫⁻ x, g x ∂(poissonRandomMeasure K X ω)) < ⊤ := by
  have hm : Measurable fun ω =>
      ∫⁻ x, g x ∂(poissonRandomMeasure K X ω) :=
    measurable_lintegral_poissonRandomMeasure
      hd.measurable_count hd.measurable_point hg
  apply ae_lt_top hm
  rw [lintegral_lintegral_poissonRandomMeasure hd hg]
  exact hfinite.ne

theorem IsPoissonPointFamily.ae_lintegral_restrict_poissonRandomMeasure_lt_top
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {A : Set E} (hA : MeasurableSet A)
    {g : E → ENNReal} (hg : Measurable g)
    (hfinite : (∫⁻ x in A, g x ∂m) < ⊤) :
    ∀ᵐ ω ∂P, (∫⁻ x in A, g x ∂(poissonRandomMeasure K X ω)) < ⊤ := by
  have h := hd.ae_lintegral_poissonRandomMeasure_lt_top
    (hg.indicator hA) (by simpa only [lintegral_indicator hA] using hfinite)
  simpa only [lintegral_indicator hA] using h

end ProbabilityTheory
