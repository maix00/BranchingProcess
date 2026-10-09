/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.SourcePath
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.InnerOuter
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Mogul'skii rates under arbitrary i.i.d. realizations

The exact target in class M need not be measurable. We transfer the
probabilities only for its M₃ approximants, whose path events are
null-measurable under the induced path law, and then apply the existing
measure-theoretic inner/outer squeeze.
-/

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk

/-- A finite-union corridor event has the same probability under any i.i.d.
realization and the canonical sequence law. The path corridor is
null-measurable under the induced path law, which is the hypothesis needed
for Measure.map_apply₀; no arbitrary-set pushforward formula is used. -/
theorem measure_sourceFiniteCorridorUnionEvent_eq_of_iid
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ) (n : ℕ) {α : ℝ} (C : FiniteCorridorUnion α) :
    P {ω | sourceNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ C.toSet} =
      iidSequenceLaw ν {increment |
        sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet} := by
  let pathMap : (ℕ → ℝ) → CadlagPath unitInterval ℝ :=
    sourceNormalizedStepCadlagPathIcc scale n
  let pathLaw : Measure (CadlagPath unitInterval ℝ) :=
    (iidSequenceLaw ν).map pathMap
  let realizedPath : Ω → CadlagPath unitInterval ℝ := fun ω =>
    pathMap (fun k => coordinate k ω)
  have hrealizedLaw : HasLaw realizedPath pathLaw P := by
    simpa [realizedPath, pathLaw, pathMap] using
      hasLaw_sourceNormalizedStepCadlagPathIcc_of_iid
        hindep hmeasurable hlaw scale n
  have hpathEvent : NullMeasurableSet C.toSet pathLaw := by
    dsimp [pathLaw]
    exact ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.FiniteCorridorUnion.nullMeasurableSet_toSet C _
  have hrealizedPathEvent : NullMeasurableSet C.toSet (P.map realizedPath) := by
    rw [hrealizedLaw.map_eq]
    exact hpathEvent
  calc
    P {ω | realizedPath ω ∈ C.toSet} = P.map realizedPath C.toSet :=
      (Measure.map_apply₀ hrealizedLaw.aemeasurable hrealizedPathEvent).symm
    _ = pathLaw C.toSet := by rw [hrealizedLaw.map_eq]
    _ = iidSequenceLaw ν {increment | pathMap increment ∈ C.toSet} := by
      dsimp [pathLaw]
      exact Measure.map_apply₀
        (measurable_sourceNormalizedStepCadlagPathIcc scale n).aemeasurable
        (by simpa [pathLaw, pathMap] using hpathEvent)

/-- The inner and outer probabilities of any source-path set in class M
have the same unique logarithmic rate under an arbitrary i.i.d. realization.
The canonical M₃ rates are transferred through null-measurable corridor
events; no measurability assumption on G is required. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_iid
    {Ω : Type*} [MeasurableSpace Ω]
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
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    ∃! H : ℝ,
      ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy ∧
        (∀ᶠ n : ℕ in atTop,
          0 < ((P.innerMeasure {ω |
            sourceNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal)) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (P {ω |
            sourceNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal) ∧
        0 < H ∧ H ≤ FiniteCorridorUnion.realEnergy (A.inner 0) ∧
        Tendsto (fun n : ℕ => Real.log
          ((P.innerMeasure {ω |
            sourceNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal) / g n)
          atTop (𝓝 (κ * H)) ∧
        Tendsto (fun n : ℕ => Real.log ((P {ω |
          sourceNormalizedStepCadlagPathIcc scale n
            (fun k => coordinate k ω) ∈ G}).toReal) / g n)
          atTop (𝓝 (κ * H)) := by
  let paths : ℕ → Ω → CadlagPath unitInterval ℝ := fun n ω =>
    sourceNormalizedStepCadlagPathIcc scale n (fun k => coordinate k ω)
  have hcoordinates : Measurable (fun ω k => coordinate k ω) :=
    measurable_pi_iff.mpr hmeasurable
  have hpathsMeasurable (n : ℕ) : Measurable (paths n) := by
    dsimp [paths]
    exact (measurable_sourceNormalizedStepCadlagPathIcc scale n).comp hcoordinates
  have hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ n : ℕ, NullMeasurableSet {ω | paths n ω ∈ C.toSet} P) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (P {ω | paths n ω ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log (P {ω | paths n ω ∈ C.toSet}).toReal / g n)
        atTop (𝓝 (κ * C.realEnergy)) := by
    intro C
    refine ⟨?_, ?_, ?_⟩
    · intro n
      let pathLaw : Measure (CadlagPath unitInterval ℝ) :=
        (iidSequenceLaw ν).map (sourceNormalizedStepCadlagPathIcc scale n)
      have hpathLaw : HasLaw (paths n) pathLaw P := by
        simpa [paths, pathLaw] using
          hasLaw_sourceNormalizedStepCadlagPathIcc_of_iid
            hindep hmeasurable hlaw scale n
      have hpathEvent : NullMeasurableSet C.toSet pathLaw := by
        dsimp [pathLaw]
        exact ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability.FiniteCorridorUnion.nullMeasurableSet_toSet C _
      have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving
          (paths n) P pathLaw := by
        rw [← hpathLaw.map_eq]
        exact (hpathsMeasurable n).quasiMeasurePreserving P
      change NullMeasurableSet ((paths n) ⁻¹' C.toSet) P
      exact hpathEvent.preimage hqmp
    · have hpositive := (hcanonicalFiniteUnionRate C).1
      filter_upwards [hpositive] with n hn
      rw [measure_sourceFiniteCorridorUnionEvent_eq_of_iid hindep hmeasurable hlaw scale n C]
      exact hn
    · have heq :
          (fun n : ℕ => Real.log
            (P {ω | paths n ω ∈ C.toSet}).toReal / g n) =ᶠ[atTop]
          (fun n : ℕ => Real.log (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
              g n) := by
        filter_upwards [] with n
        simp only [paths]
        rw [measure_sourceFiniteCorridorUnionEvent_eq_of_iid
          hindep hmeasurable hlaw scale n C]
      exact (hcanonicalFiniteUnionRate C).2.congr' heq.symm
  have hUnique := existsUnique_commonEnergy_of_hasVanishingEnergyGapApproximation P paths g hg hκ hG hFiniteUnionRate
  obtain ⟨A, hLimits, hInnerPositive, hOuterPositive,
      hInnerRate, hOuterRate, hEnergyBounds⟩ :=
    exists_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation
      P paths g hg hκ hG hFiniteUnionRate
  refine ⟨hLimits.commonEnergy, ?_, ?_⟩
  · exact ⟨A, hLimits, rfl, hInnerPositive, hOuterPositive,
      hEnergyBounds.1, hEnergyBounds.2, hInnerRate, hOuterRate⟩
  · intro H hH
    obtain ⟨A', hLimits', hEq', _hInnerPositive', _hOuterPositive',
        _hPositive', _hEnergyUpper', _hInnerRate', _hOuterRate'⟩ := hH
    exact hUnique.unique ⟨A', hLimits', hEq'⟩ ⟨A, hLimits, rfl⟩

/-- Relative `M` rates also transfer to arbitrary i.i.d. realizations when
every realized path lies in the source domain. The finite corridor rates are
transferred from the canonical sequence law through the same law identity as
in the unrestricted result. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_iid
    {Ω : Type*} [MeasurableSpace Ω]
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
    {G : Set (CadlagPath unitInterval ℝ)}
    (hG : HasRelativeVanishingEnergyGapApproximation α
      Skorokhod.terminalLeftPathSpace G) :
    ∃! H : ℝ,
      ∃ A : RelativeFiniteCorridorUnionApproximation α
          Skorokhod.terminalLeftPathSpace G,
        ∃ hLimits : RelativeFiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy ∧
          (∀ᶠ n : ℕ in atTop,
            0 < (P.innerMeasure {ω |
              sourceNormalizedStepCadlagPathIcc scale n
                (fun k => coordinate k ω) ∈ G}).toReal) ∧
          (∀ᶠ n : ℕ in atTop,
            0 < (P {ω |
              sourceNormalizedStepCadlagPathIcc scale n
                (fun k => coordinate k ω) ∈ G}).toReal) ∧
          Tendsto (fun n : ℕ => Real.log
            ((P.innerMeasure {ω |
              sourceNormalizedStepCadlagPathIcc scale n
                (fun k => coordinate k ω) ∈ G}).toReal) / g n)
            atTop (𝓝 (κ * H)) ∧
          Tendsto (fun n : ℕ => Real.log (P {ω |
            sourceNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal / g n)
            atTop (𝓝 (κ * H)) := by
  let paths : ℕ → Ω → CadlagPath unitInterval ℝ := fun n ω =>
    sourceNormalizedStepCadlagPathIcc scale n (fun k => coordinate k ω)
  have hcoordinates : Measurable (fun ω k => coordinate k ω) :=
    measurable_pi_iff.mpr hmeasurable
  have hpathsMeasurable (n : ℕ) : Measurable (paths n) := by
    dsimp [paths]
    exact (measurable_sourceNormalizedStepCadlagPathIcc scale n).comp hcoordinates
  have hpaths : ∀ n ω, paths n ω ∈ Skorokhod.terminalLeftPathSpace := by
    intro n ω
    exact Skorokhod.terminalLeftPath_mem_space
      (normalizedStepCadlagPathIcc scale n (fun k => coordinate k ω))
  have hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ n : ℕ, NullMeasurableSet {ω | paths n ω ∈ C.toSet} P) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (P {ω | paths n ω ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log (P {ω | paths n ω ∈ C.toSet}).toReal / g n)
        atTop (𝓝 (κ * C.realEnergy)) := by
    intro C
    refine ⟨?_, ?_, ?_⟩
    · intro n
      let pathLaw : Measure (CadlagPath unitInterval ℝ) :=
        (iidSequenceLaw ν).map (sourceNormalizedStepCadlagPathIcc scale n)
      have hpathLaw : HasLaw (paths n) pathLaw P := by
        simpa [paths, pathLaw] using
          hasLaw_sourceNormalizedStepCadlagPathIcc_of_iid
            hindep hmeasurable hlaw scale n
      have hpathEvent : NullMeasurableSet C.toSet pathLaw := by
        dsimp [pathLaw]
        exact FiniteCorridorUnion.nullMeasurableSet_toSet C _
      have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (paths n) P pathLaw := by
        rw [← hpathLaw.map_eq]
        exact (hpathsMeasurable n).quasiMeasurePreserving P
      change NullMeasurableSet ((paths n) ⁻¹' C.toSet) P
      exact hpathEvent.preimage hqmp
    · have hpositive := (hcanonicalFiniteUnionRate C).1
      filter_upwards [hpositive] with n hn
      rw [measure_sourceFiniteCorridorUnionEvent_eq_of_iid hindep hmeasurable hlaw scale n C]
      exact hn
    · have heq : (fun n : ℕ =>
          Real.log (P {ω | paths n ω ∈ C.toSet}).toReal / g n) =ᶠ[atTop]
          fun n : ℕ => Real.log (iidSequenceLaw ν
            {increment : ℕ → ℝ |
              sourceNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
            g n := by
        filter_upwards [] with n
        simpa [paths] using congrArg
          (fun x : ℝ≥0∞ => Real.log x.toReal / g n)
          (measure_sourceFiniteCorridorUnionEvent_eq_of_iid hindep hmeasurable hlaw scale n C)
      exact (hcanonicalFiniteUnionRate C).2.congr' heq.symm
  exact existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation
    P paths Skorokhod.terminalLeftPathSpace hpaths g hg hκ hG hFiniteUnionRate

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
