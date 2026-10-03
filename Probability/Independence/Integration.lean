module

public import Mathlib.Probability.Independence.Integration

/-!
# Integrals over independent events

These factorization lemmas specialize independence of functions to indicators
of measurable events. They are probability facts, separate from deterministic
truncation bounds.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory

/-- An integrable observable independent of a measurable event gains the
probability of that event exactly. -/
theorem integral_abs_mul_indicator_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (E : Set Ω)
    (hf : Integrable f μ) (hE : MeasurableSet E)
    (hind : IndepFun (fun ω => |f ω|) (E.indicator (fun _ => (1 : ℝ))) μ) :
    (∫ ω, |f ω| * E.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      (∫ ω, |f ω| ∂μ) * μ.real E := by
  have habs : AEStronglyMeasurable (fun ω => |f ω|) μ :=
    hf.abs.aestronglyMeasurable
  have hfactor := hind.integral_mul_eq_mul_integral habs
    (measurable_const.indicator hE).aestronglyMeasurable
  change μ[(fun ω => |f ω|) * E.indicator (fun _ => (1 : ℝ))] = _
  rw [hfactor, integral_indicator_const (1 : ℝ) hE]
  simp

/-- A finite sum of integrable observables gains the probability of an event
term by term when every observable is independent of that event. Mutual
independence of the observables is not required. -/
theorem integral_sum_abs_mul_indicator_eq
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (f : ι → Ω → ℝ) (E : Set Ω)
    (hf : ∀ i ∈ s, Integrable (f i) μ) (hE : MeasurableSet E)
    (hind : ∀ i ∈ s,
      IndepFun (fun ω => |f i ω|) (E.indicator (fun _ => (1 : ℝ))) μ) :
    (∫ ω, (∑ i ∈ s, |f i ω|) * E.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      (∑ i ∈ s, ∫ ω, |f i ω| ∂μ) * μ.real E := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_abs_mul_indicator_eq μ (f i) E (hf i hi) hE (hind i hi)
  · intro i hi
    have hint := (hf i hi).abs.indicator hE
    convert hint using 1
    ext ω
    by_cases hω : ω ∈ E <;> simp [hω]

/-- Sigma-algebra form of `integral_abs_mul_indicator_eq`. -/
theorem integral_abs_mul_indicator_eq_of_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (mPast : MeasurableSpace Ω) (f : Ω → ℝ) (E : Set Ω)
    (hf : Integrable f μ)
    (hE : MeasurableSet[mPast] E) (hEfull : MeasurableSet[mΩ] E)
    (hind : Indep mPast (MeasurableSpace.comap f inferInstance) μ) :
    (∫ ω, |f ω| * E.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
      (∫ ω, |f ω| ∂μ) * μ.real E := by
  have hindicator :
      (E.indicator (fun _ => (1 : ℝ))) ⟂ᵢ[μ] f :=
    hind.indicator_indepFun (1 : ℝ) hE
  have habs :
      (fun ω => |f ω|) ⟂ᵢ[μ] E.indicator (fun _ => (1 : ℝ)) := by
    have hcomp := hindicator.symm.comp
      (by fun_prop : Measurable fun x : ℝ => |x|) measurable_id
    simpa [Function.comp_def] using hcomp
  exact @integral_abs_mul_indicator_eq Ω mΩ μ f E hf hEfull habs

end ProbabilityTheory

end
