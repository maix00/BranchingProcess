/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
import Probability.BranchingProcess.GaltonWatson.BranchingProperty
import Probability.BranchingProcess.Offspring.PointMeasure
import Probability.BranchingRandomWalk.Genealogy.GaltonWatson
import Combinatorics.BranchingWalk.StepField
import Mathlib.Probability.Independence.InfinitePi

noncomputable section

/-!
# Galton--Watson law interface checks

The general presampled law accepts an offspring configuration law directly,
allows an all-absent offspring configuration, and inherits the shared
generation-size observation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

private def emptyConfiguration : Combinatorics.Branching.Step Unit PUnit.{1} :=
  fun _ => none

private noncomputable def emptyOffspringLaw :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw Unit PUnit.{1} :=
  Measure.dirac emptyConfiguration |>.toProbabilityMeasure

private def emptyField : Combinatorics.Branching.StepField Unit PUnit.{1} :=
  fun _ => emptyConfiguration

private def emptyProcess : Combinatorics.Branching.Process Unit :=
  Combinatorics.Branching.branchingOfStepField emptyField

private def fullField : Combinatorics.Branching.StepField ℕ PUnit.{1} :=
  fun _ _ => some PUnit.unit

private def fullProcess : Combinatorics.Branching.Process ℕ :=
  Combinatorics.Branching.branchingOfStepField fullField

private def duplicateMarkConfiguration :
    Combinatorics.Branching.Step (Fin 2) ℕ :=
  fun _ => some 7

private def noBirthField : Combinatorics.Branching.StepField ℕ PUnit.{1} :=
  fun _ _ => none

/-- A sampled child at this address is unreachable because the root has no
children. -/
private def hiddenBirthField : Combinatorics.Branching.StepField ℕ PUnit.{1} :=
  fun u _ => if u = [0] then some PUnit.unit else none

private def noBirthProcess : Combinatorics.Branching.Process ℕ :=
  Combinatorics.Branching.branchingOfStepField noBirthField

private def hiddenBirthProcess : Combinatorics.Branching.Process ℕ :=
  Combinatorics.Branching.branchingOfStepField hiddenBirthField

example : ProbabilityMeasure (Combinatorics.Branching.Process Unit) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.law emptyOffspringLaw

example (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw Unit PUnit.{1}) :
    iIndepFun
      (fun u (field : Combinatorics.Branching.StepField Unit PUnit.{1}) => field u)
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField Unit PUnit.{1})) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.field_independent μ

example (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw Unit PUnit.{1}) :
    ((ProbabilityTheory.BranchingProcess.GaltonWatson.law μ :
      ProbabilityMeasure (Combinatorics.Branching.Process Unit)) :
      Measure (Combinatorics.Branching.Process Unit)).map
        (fun β => β.step PUnit.unit) =
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField Unit PUnit.{1})) :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.law_stepField μ

example (β : Combinatorics.Branching.Process Unit) : β.generationSize 0 = 1 :=
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_zero β

example : emptyProcess.generationSize 1 = 0 := by
  rw [Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_one_eq_childCount]
  simp [emptyProcess, emptyField, emptyConfiguration,
    Combinatorics.Branching.Step.childCount,
    Combinatorics.Branching.support, Combinatorics.Branching.survive]

example : fullProcess.generationSize 1 = ⊤ := by
  rw [Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_one_eq_childCount]
  simp [fullProcess, fullField, Combinatorics.Branching.Step.childCount,
    Combinatorics.Branching.support, Combinatorics.Branching.survive]

example : duplicateMarkConfiguration.childCount = 2 := by
  simp [Combinatorics.Branching.Step.childCount,
    Combinatorics.Branching.support, Combinatorics.Branching.survive,
    duplicateMarkConfiguration]

example : Combinatorics.Branching.stepPointMeasure duplicateMarkConfiguration
    Set.univ = 2 := by
  rw [Combinatorics.Branching.stepPointMeasure_univ]
  norm_num [Combinatorics.Branching.Step.childCount,
    Combinatorics.Branching.support, Combinatorics.Branching.survive,
    duplicateMarkConfiguration]

example (β : Combinatorics.Branching.BranchingWalk ℕ ℕ ℕ) :
    β.toBranching.generationSize 1 = β.generationSize 1 :=
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_toBranching β 1

example : (ProbabilityTheory.BranchingProcess.GaltonWatson.law emptyOffspringLaw).map
    (fun β : Combinatorics.Branching.Process Unit => β.generationSize 1) =
      emptyOffspringLaw.childCountLaw :=
  ProbabilityTheory.BranchingProcess.GaltonWatson.generationSize_one_law
    emptyOffspringLaw

example : noBirthProcess ≠ hiddenBirthProcess := by
  intro h
  have hfield := congrArg (fun β : Combinatorics.Branching.Process ℕ =>
    β.step PUnit.unit) h
  have hslot := congrArg (fun field : Combinatorics.Branching.StepField ℕ PUnit.{1} =>
    field [0] 0) hfield
  change noBirthField [0] 0 = hiddenBirthField [0] 0 at hslot
  simp [noBirthField, hiddenBirthField] at hslot

example :
    Combinatorics.Branching.survivingParticles noBirthProcess =
      Combinatorics.Branching.survivingParticles hiddenBirthProcess := by
  ext p
  rcases p with ⟨r, u⟩
  cases r
  rw [Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong
      noBirthProcess PUnit.unit u,
    Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong
      hiddenBirthProcess PUnit.unit u]
  cases u <;>
    simp [Combinatorics.Branching.surviveAlong, noBirthProcess,
      hiddenBirthProcess, Combinatorics.Branching.branchingOfStepField,
      noBirthField, hiddenBirthField, Combinatorics.Branching.survive]

example (β : Combinatorics.Branching.Process Unit) {n m : ℕ} (hnm : n ≤ m)
    (hzero : β.generationSize n = 0) : β.generationSize m = 0 :=
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_eq_zero_of_le
    β hnm hzero

example {ι Mark : Type*} [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (u : Combinatorics.UlamHarris.TreeNode ι) :
    (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι Mark)).map
        (fun field => field u) =
      (μ : Measure (Combinatorics.Branching.Step ι Mark)) :=
  ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_coordinate μ u

example {ι Mark : Type*} [Countable ι] [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ProbabilityMeasure (Measure Mark) :=
  μ.pointMeasureLaw

example {ι Mark Mark' : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).pointMeasureLaw =
      μ.pointMeasureLaw.map (Measure.map f) :=
  ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.pointMeasureLaw_mapMarks
    μ f hf

example {ι Mark Mark' : Type*} [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).fieldLaw =
      (μ.fieldLaw).map (Combinatorics.Branching.StepField.map f) :=
  ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_mapMarks
    μ f hf

example {ι Mark : Type*} [MeasurableSpace Mark]
    (ξ : Combinatorics.Branching.Step ι Mark) :
    Combinatorics.Branching.stepPointMeasure ξ Set.univ =
      (ξ.childCount : ℝ≥0∞) :=
  Combinatorics.Branching.stepPointMeasure_univ ξ

#print axioms
  Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize_one_eq_childCount

#print axioms
  ProbabilityTheory.BranchingProcess.GaltonWatson.generationSize_one_law
