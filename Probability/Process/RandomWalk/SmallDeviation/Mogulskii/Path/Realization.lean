/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.InnerOuter
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
public import Probability.Sequence.IID.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Path.Lemmas

/-!
# Mogul'skii rates under arbitrary i.i.d. realizations

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.existsUnique_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_iid`:
  if finite corridor unions have rate $\kappa E(C)$ under the canonical
  law, an $M_3$ path class has a unique energy $H$ and both realized
  inner and outer logarithmic rates equal $\kappa H$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_iid`:
  the same conclusion holds for a relative $M_3$ class in the source
  terminal-left path domain.

The target in class M is handled through its M₃ approximants, whose path
events are null-measurable under the induced path law. The existing
measure-theoretic inner/outer squeeze then gives the two rates.

The terminal-left path-class rate is A. A. Mogul'skii, Theorem 3, Section 4, p. 764,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk

/-- The inner and outer probabilities of any terminal-left path set in class M
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
          terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
          g n) atTop (𝓝 (κ * C.realEnergy)))
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G) :
    ∃! H : ℝ,
      ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
        H = hLimits.commonEnergy ∧
        (∀ᶠ n : ℕ in atTop,
          0 < ((P.innerMeasure {ω |
            terminalLeftNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal)) ∧
        (∀ᶠ n : ℕ in atTop,
          0 < (P {ω |
            terminalLeftNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal) ∧
        0 < H ∧ H ≤ FiniteCorridorUnion.realEnergy (A.inner 0) ∧
        Tendsto (fun n : ℕ => Real.log
          ((P.innerMeasure {ω |
            terminalLeftNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal) / g n)
          atTop (𝓝 (κ * H)) ∧
        Tendsto (fun n : ℕ => Real.log ((P {ω |
          terminalLeftNormalizedStepCadlagPathIcc scale n
            (fun k => coordinate k ω) ∈ G}).toReal) / g n)
          atTop (𝓝 (κ * H)) := by
  let paths : ℕ → Ω → CadlagPath unitInterval ℝ := fun n ω =>
    terminalLeftNormalizedStepCadlagPathIcc scale n (fun k => coordinate k ω)
  have hcoordinates : Measurable (fun ω k => coordinate k ω) :=
    measurable_pi_iff.mpr hmeasurable
  have hpathsMeasurable (n : ℕ) : Measurable (paths n) := by
    dsimp [paths]
    exact (measurable_terminalLeftNormalizedStepCadlagPathIcc scale n).comp hcoordinates
  have hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ n : ℕ, NullMeasurableSet {ω | paths n ω ∈ C.toSet} P) ∧
      (∀ᶠ n : ℕ in atTop, 0 < (P {ω | paths n ω ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log (P {ω | paths n ω ∈ C.toSet}).toReal / g n)
        atTop (𝓝 (κ * C.realEnergy)) := by
    intro C
    refine ⟨?_, ?_, ?_⟩
    · intro n
      let pathLaw : Measure (CadlagPath unitInterval ℝ) :=
        (iidSequenceLaw ν).map (terminalLeftNormalizedStepCadlagPathIcc scale n)
      have hpathLaw : HasLaw (paths n) pathLaw P := by
        simpa [paths, pathLaw] using
          hasLaw_terminalLeftNormalizedStepCadlagPathIcc_of_iid
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
              terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
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
          terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal) ∧
      Tendsto (fun n : ℕ => Real.log (iidSequenceLaw ν
        {increment : ℕ → ℝ |
          terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
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
              terminalLeftNormalizedStepCadlagPathIcc scale n
                (fun k => coordinate k ω) ∈ G}).toReal) ∧
          (∀ᶠ n : ℕ in atTop,
            0 < (P {ω |
              terminalLeftNormalizedStepCadlagPathIcc scale n
                (fun k => coordinate k ω) ∈ G}).toReal) ∧
          Tendsto (fun n : ℕ => Real.log
            ((P.innerMeasure {ω |
              terminalLeftNormalizedStepCadlagPathIcc scale n
                (fun k => coordinate k ω) ∈ G}).toReal) / g n)
            atTop (𝓝 (κ * H)) ∧
          Tendsto (fun n : ℕ => Real.log (P {ω |
            terminalLeftNormalizedStepCadlagPathIcc scale n
              (fun k => coordinate k ω) ∈ G}).toReal / g n)
            atTop (𝓝 (κ * H)) := by
  let paths : ℕ → Ω → CadlagPath unitInterval ℝ := fun n ω =>
    terminalLeftNormalizedStepCadlagPathIcc scale n (fun k => coordinate k ω)
  have hcoordinates : Measurable (fun ω k => coordinate k ω) :=
    measurable_pi_iff.mpr hmeasurable
  have hpathsMeasurable (n : ℕ) : Measurable (paths n) := by
    dsimp [paths]
    exact (measurable_terminalLeftNormalizedStepCadlagPathIcc scale n).comp hcoordinates
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
        (iidSequenceLaw ν).map (terminalLeftNormalizedStepCadlagPathIcc scale n)
      have hpathLaw : HasLaw (paths n) pathLaw P := by
        simpa [paths, pathLaw] using
          hasLaw_terminalLeftNormalizedStepCadlagPathIcc_of_iid
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
              terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet}).toReal /
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
