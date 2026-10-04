module

public import Probability.RandomMeasure.Poisson.Basic
import Probability.Process.Levy.Jump.IntegralBound

@[expose] public section

/-!
# Poisson small-jump path bound

The generic deterministic variation estimate applied to a realized Poisson
random measure.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- The pointwise small-path bound for a Poisson jump measure follows from
one bound on its realized absolute-jump integral. -/
theorem poissonRandomMeasure_smallJumpPath_bound
    {Ω Time Mark : Type} [MeasurableSpace Ω]
    [Preorder Time] [MeasurableSpace Time] [MeasurableSpace Mark]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → Time × Mark}
    (ω : Ω) (A : Set (Time × Mark)) (f : Mark → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hV : (∫⁻ z in A, ENNReal.ofReal |f z.2|
      ∂(poissonRandomMeasure K X ω)) < ENNReal.ofReal ρ) :
    ∀ t : Time,
      |∫ z in {z | z ∈ A ∧ z.1 ≤ t}, f z.2
        ∂(poissonRandomMeasure K X ω)| ≤ ρ := by
  exact abs_jumpIntegral_le_of_totalVariation_lt
    (poissonRandomMeasure K X ω) A f ρ hρ hV

end ProbabilityTheory
