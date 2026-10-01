module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Pathwise variation bound for jump integrals

The integral of jump marks over any observed time slice is controlled by the
total absolute jump mass on the full small-jump region. The statement is
deterministic and applies to each realization of a random point measure.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem enorm_integral_restrict_le_lintegral_abs
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (f : E → ℝ) {B A : Set E} (hBA : B ⊆ A) :
    ENNReal.ofReal |∫ x in B, f x ∂ν| ≤
      ∫⁻ x in A, ENNReal.ofReal |f x| ∂ν := by
  have h := enorm_integral_le_lintegral_enorm
    (μ := ν.restrict B) f
  have hmono := lintegral_mono_set (μ := ν)
    (f := fun x => ENNReal.ofReal |f x|) hBA
  have h' : ENNReal.ofReal |∫ x in B, f x ∂ν| ≤
      ∫⁻ x in B, ENNReal.ofReal |f x| ∂ν := by
    simpa only [Real.enorm_eq_ofReal_abs] using h
  exact h'.trans hmono

/-- A strict bound on total absolute variation gives the same strict bound
for the displacement integral over every smaller observation set. -/
theorem abs_integral_restrict_lt_of_lintegral_abs_lt
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (f : E → ℝ) {B A : Set E} (hBA : B ⊆ A)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hV : (∫⁻ x in A, ENNReal.ofReal |f x| ∂ν) < ENNReal.ofReal ρ) :
    |∫ x in B, f x ∂ν| < ρ := by
  have hbound := (enorm_integral_restrict_le_lintegral_abs ν f hBA).trans_lt hV
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp hbound

/-- One total-variation bound controls the displacement at every time on the
same realization; the time index need only have an order. -/
theorem abs_jumpIntegral_le_of_totalVariation_lt
    {Time Mark : Type*} [Preorder Time]
    [MeasurableSpace Time] [MeasurableSpace Mark]
    (ν : Measure (Time × Mark)) (A : Set (Time × Mark))
    (f : Mark → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hV : (∫⁻ z in A, ENNReal.ofReal |f z.2| ∂ν) < ENNReal.ofReal ρ) :
    ∀ t : Time,
      |∫ z in {z | z ∈ A ∧ z.1 ≤ t}, f z.2 ∂ν| ≤ ρ := by
  intro t
  exact (abs_integral_restrict_lt_of_lintegral_abs_lt ν (fun z => f z.2)
    (by intro z hz; exact hz.1) ρ hρ hV).le

end ProbabilityTheory

end
