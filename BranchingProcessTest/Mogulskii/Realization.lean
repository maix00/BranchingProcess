import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Realization

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal Topology

example {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ) {α : ℝ} (C : FiniteCorridorUnion α) (n : ℕ) :
    P {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ C.toSet} =
      iidSequenceLaw ν {increment |
        sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet} :=
  measure_sourceFiniteCorridorUnionEvent_eq_of_iid
    hindep hmeasurable hlaw scale n C

example {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α κ : ℝ} {g : ℕ → ℝ}
    (hg : Tendsto g atTop atBot) (hκ : 0 < κ)
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ)
    (hcanonicalFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ᶠ n : ℕ in atTop, 0 < (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
          g n) atTop (𝓝 (κ * C.realEnergy)))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :=
  existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_iid
    P hg hκ hindep hmeasurable hlaw scale hcanonicalFiniteUnionRate hG

#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.measure_sourceFiniteCorridorUnionEvent_eq_of_iid
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_iid
