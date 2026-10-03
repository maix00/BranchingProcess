import Probability.RandomMeasure.Poisson.Integral

/-!
# Finite vectors of Poisson window integrals

This module builds a finite real vector by integrating the mark over each
time window in each of two independent Poisson random measure models.
-/

open MeasureTheory

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- The vector of window increments in the sum of two Poisson random
measures. -/
noncomputable def poissonWindowIntegralVector
    {ι : Type*} {Ωs Ωb : Type} [Fintype ι]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    (S : ι → Set unitInterval)
    [decS : ∀ i, DecidablePred (fun z : unitInterval × ℝ => z.1 ∈ S i)]
    (ω : Ωs × Ωb) : ι → ℝ := fun i =>
  (∫ z : unitInterval × ℝ, (if z.1 ∈ S i then z.2 else 0 : ℝ)
    ∂(poissonRandomMeasure (Ω := Ωs) (E := unitInterval × ℝ) Ks Xs ω.1)) +
  (∫ z : unitInterval × ℝ, (if z.1 ∈ S i then z.2 else 0 : ℝ)
    ∂(poissonRandomMeasure (Ω := Ωb) (E := unitInterval × ℝ) Kb Xb ω.2))

/-- The finite vector of window integrals is almost-everywhere measurable
when each realized window integrand is almost surely integrable. -/
theorem poissonWindowIntegralVector_aemeasurable
    {ι : Type*} {Ωs Ωb : Type} [Fintype ι]
    [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {νs νb : Measure (unitInterval × ℝ)} [SigmaFinite νs] [SigmaFinite νb]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs νs Ps)
    (hdb : IsPoissonPointFamily Kb Xb νb Pb)
    (S : ι → Set unitInterval)
    [decS : ∀ i, DecidablePred (fun z : unitInterval × ℝ => z.1 ∈ S i)]
    (hS : ∀ i, MeasurableSet (S i))
    (hsi : ∀ i, ∀ᵐ ω : Ωs ∂Ps, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Ks Xs ω))
    (hbi : ∀ i, ∀ᵐ ω : Ωb ∂Pb, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Kb Xb ω)) :
    AEMeasurable (poissonWindowIntegralVector
      (Ks := Ks) (Xs := Xs) (Kb := Kb) (Xb := Xb) S) (Ps.prod Pb) := by
  apply AEMeasurable.of_eval
  intro i
  have hmeas : Measurable (fun z : unitInterval × ℝ =>
      if z.1 ∈ S i then z.2 else 0) := by
    exact Measurable.ite ((hS i).preimage measurable_fst) measurable_snd measurable_const
  exact (hds.aemeasurable_integral_poissonRandomMeasure hmeas (hsi i)).comp_fst.add
    (hdb.aemeasurable_integral_poissonRandomMeasure hmeas (hbi i)).comp_snd

end ProbabilityTheory
