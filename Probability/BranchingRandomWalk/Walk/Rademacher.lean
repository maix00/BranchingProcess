import Probability.BranchingRandomWalk.Walk.Law
import Probability.Distributions.Rademacher

/-!
# The Rademacher random walk

This file realizes the canonical IID Rademacher increment process through the
project's `RandomWalk`, which is the singleton-slot specialization of a
branching random walk.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching
open Combinatorics.Branching.Walk

/-- Turn a Boolean branch sequence into its real Rademacher increment path. -/
def rademacherIncrementPath (branch : ℕ → Bool) : ℕ → ℝ :=
  fun n => rademacherOfBool (branch n)

theorem measurable_rademacherIncrementPath :
    Measurable rademacherIncrementPath := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_rademacherOfBool.comp (measurable_pi_apply n)

/-- Pushing the canonical fair-Boolean IID law through the pointwise encoding
gives the canonical real Rademacher increment law. -/
theorem map_iidSequenceLaw_rademacherIncrementPath :
    (iidSequenceLaw fairBoolMeasure).map rademacherIncrementPath =
      independentIncrementLaw rademacherMeasure := by
  unfold iidSequenceLaw independentIncrementLaw rademacherIncrementPath
  rw [Measure.infinitePi_map_pi]
  · simp_rw [map_fairBernoulli_rademacherOfBool]
    rfl
  · exact fun _ => measurable_rademacherOfBool

/-- The everywhere-present random walk with IID Rademacher increments. -/
noncomputable def rademacher (initial : ℝ) : RandomWalk ℝ ℝ :=
  ofIncrementLaw initial (independentIncrementLaw rademacherMeasure)

@[simp]
theorem rademacher_law (initial : ℝ) :
    (rademacher initial).law =
      (independentIncrementLaw rademacherMeasure).map
        (Walk.ofIncrements initial) := rfl

/-- The Rademacher random walk is realized by an increment path. -/
theorem rademacher_isIncrementPathRealization (initial : ℝ) :
    IsIncrementPathRealization (rademacher initial) :=
  isIncrementPathRealization_ofIncrementLaw initial
    (independentIncrementLaw rademacherMeasure)

/-- Hence the canonical Rademacher random walk survives forever. -/
theorem rademacher_survivesForever (initial : ℝ) :
    SurvivesForever (rademacher initial) :=
  survivesForever_ofIncrementLaw initial
    (independentIncrementLaw rademacherMeasure)

/-- Along an increment realization, the process position is the project's
usual partial sum added to the initial position. -/
theorem process_ofIncrements_eq_partialSum
    (initial : ℝ) (increment : ℕ → ℝ) (n : ℕ) :
    process id n (Walk.ofIncrements initial increment) =
      some (initial + partialSum n increment) := by
  simp [positionProcess]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
