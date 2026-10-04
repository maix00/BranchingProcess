/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Law
public import Probability.Distributions.Rademacher

/-!
# The Rademacher increment law

This file realizes the canonical IID Rademacher increment law as a
process-level random walk, independently of any branching-walk realization.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

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

end ProbabilityTheory.RandomWalk
