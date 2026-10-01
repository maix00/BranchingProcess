import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Probability.Process.Levy.Jump.VariationLimit

/-!
# Campbell's identity on a measurable jump region

This applies the general Poisson random measure identity from LeanLevy to a
truncated jump band, the form needed for small-jump variation estimates.
-/

namespace ProbabilityTheory

open MeasureTheory
open Filter

theorem lintegral_poissonRandomMeasure_restrict
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    (A : Set E) (hA : MeasurableSet A)
    (weight : E → ENNReal) (hweight : Measurable weight) :
    (∫⁻ ω, ∫⁻ x in A, weight x ∂(poissonRandomMeasure K X ω) ∂P) =
      ∫⁻ x in A, weight x ∂m := by
  have h := lintegral_lintegral_poissonRandomMeasure hd (hweight.indicator hA)
  simpa only [lintegral_indicator hA] using h

/-- The Campbell identity and finite first jump moment give a deterministic
cutoff whose realized small-jump variation is small with positive probability. -/
theorem exists_poissonSmallVariation_pos
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂m) ≠ ⊤)
    (haway : ∀ᵐ x ∂m, ∀ᶠ n in atTop, x ∉ band n)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, 0 < P {ω | (∫⁻ x in band n, weight x ∂(poissonRandomMeasure K X ω)) <
      ENNReal.ofReal ρ} := by
  apply exists_smallVariation_pos_of_campbell m P weight band
    (fun n ω => ∫⁻ x in band n, weight x ∂(poissonRandomMeasure K X ω))
    hweight hband hfinite haway
  · intro n
    have hm := measurable_lintegral_poissonRandomMeasure
      hd.measurable_count hd.measurable_point (hweight.indicator (hband n))
    simpa only [lintegral_indicator (hband n)] using hm
  · intro n
    exact lintegral_poissonRandomMeasure_restrict hd (band n) (hband n) weight hweight
  · exact hρ

end ProbabilityTheory
