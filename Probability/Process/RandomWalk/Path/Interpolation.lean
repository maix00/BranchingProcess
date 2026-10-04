/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Interpolation
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.UnitInterval
public import Probability.Process.RandomWalk.Law
public import Probability.Process.Path.Continuous

/-!
# Laws of linearly interpolated random-walk paths
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

theorem measurable_normalizedLinearContinuousPathIcc
    (scale : ℕ → ℝ) (n : ℕ) :
    Measurable (normalizedLinearContinuousPathIcc scale n) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_const.mul (Finset.measurable_sum _ fun k _ ↦
    measurable_const.mul (measurable_pi_apply k))

theorem measurable_maxAbsUpTo (n : ℕ) :
    Measurable (maxAbsUpTo n) := by
  unfold maxAbsUpTo
  exact Finset.measurable_range_sup'' fun k _ ↦
    Measurable.abs (measurable_pi_apply k :
      Measurable (fun increment : ℕ → ℝ ↦ increment k))

theorem measurable_normalizedLinearCadlagPathIcc
    (scale : ℕ → ℝ) (n : ℕ) :
    Measurable (normalizedLinearCadlagPathIcc scale n) :=
  Skorokhod.measurable_ofContinuousMap.comp
    (measurable_normalizedLinearContinuousPathIcc scale n)

/-- Law of the normalized linearly interpolated path under canonical IID
increments. -/
noncomputable def normalizedLinearPathLaw (nu : Measure ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    Measure C(unitInterval, ℝ) :=
  (independentIncrementLaw nu).map
    (normalizedLinearContinuousPathIcc scale n)

noncomputable instance normalizedLinearPathLaw.instIsProbabilityMeasure
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure (normalizedLinearPathLaw nu scale n) := by
  unfold normalizedLinearPathLaw
  infer_instance

theorem hasLaw_normalizedLinearContinuousPathIcc
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) (n : ℕ) :
    HasLaw (normalizedLinearContinuousPathIcc scale n)
      (normalizedLinearPathLaw nu scale n) (independentIncrementLaw nu) where
  aemeasurable :=
    (measurable_normalizedLinearContinuousPathIcc scale n).aemeasurable
  map_eq := rfl

/-- Law of the same polygonal interpolation in Skorokhod path space. -/
noncomputable def normalizedLinearCadlagPathLaw (nu : Measure ℝ)
    (scale : ℕ → ℝ) (n : ℕ) :
    Measure (CadlagPath unitInterval ℝ) :=
  (independentIncrementLaw nu).map
    (normalizedLinearCadlagPathIcc scale n)

noncomputable instance normalizedLinearCadlagPathLaw.instIsProbabilityMeasure
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure (normalizedLinearCadlagPathLaw nu scale n) := by
  unfold normalizedLinearCadlagPathLaw
  infer_instance

theorem hasLaw_normalizedLinearCadlagPathIcc
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (scale : ℕ → ℝ) (n : ℕ) :
    HasLaw (normalizedLinearCadlagPathIcc scale n)
      (normalizedLinearCadlagPathLaw nu scale n)
      (independentIncrementLaw nu) where
  aemeasurable :=
    (Skorokhod.measurable_ofContinuousMap.comp
      (measurable_normalizedLinearContinuousPathIcc scale n)).aemeasurable
  map_eq := rfl

/-- The Skorokhod law is the continuous-path law pushed through the canonical
continuous inclusion. -/
theorem normalizedLinearCadlagPathLaw_eq_map
    (nu : Measure ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    normalizedLinearCadlagPathLaw nu scale n =
      (normalizedLinearPathLaw nu scale n).map
        Skorokhod.ofContinuousMap := by
  rw [normalizedLinearCadlagPathLaw, normalizedLinearPathLaw,
    Measure.map_map]
  · rfl
  · exact Skorokhod.measurable_ofContinuousMap
  · exact measurable_normalizedLinearContinuousPathIcc scale n

end ProbabilityTheory.RandomWalk
