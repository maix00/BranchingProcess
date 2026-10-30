/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.UnitInterval
public import Probability.Process.Path.Scaling.UnitInterval
public import Probability.Process.Path.Representation.Skorokhod
public import Probability.ConvergenceInDistribution.ContinuousMap.FiniteDimensional
public import Topology.Cadlag.Skorokhod.Maps.Continuous

/-!
# Brownian finite-dimensional laws in path space

This file identifies the joint evaluation laws of a continuous Brownian path
on the unit interval and of its embedding into Skorokhod space. The generic
path representation and its image law are defined under
Probability.Process.Path.Representation.Skorokhod.

## Public declarations

- `ProbabilityTheory.IsBrownianReal.hasLaw_finiteEvaluation_continuousunitIntervalPath`:
  finite evaluations of a continuous Brownian path have the Brownian
  projective-family law reindexed to the selected unit-interval times.
- `ProbabilityTheory.IsBrownianReal.hasLaw_finiteEvaluation_cadlagunitIntervalPath`:
  the same finite-dimensional law after the Skorokhod embedding.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- Pull a vector indexed by the image of a finite family of unit-interval
times back to the original family. -/
private def unitIntervalFiniteRestriction
    (I : Finset unitInterval) :
    (↑(I.image unitInterval.toNNReal) → ℝ) → (↑I → ℝ) :=
  fun x t ↦ x ⟨unitInterval.toNNReal t,
    Finset.mem_image.2 ⟨t, t.property, rfl⟩⟩

private theorem measurable_unitIntervalFiniteRestriction
    (I : Finset unitInterval) :
    Measurable (unitIntervalFiniteRestriction I) := by
  apply Measurable.of_eval
  intro t
  let q : ↑(I.image unitInterval.toNNReal) :=
    ⟨unitInterval.toNNReal t, Finset.mem_image.2 ⟨t, t.property, rfl⟩⟩
  exact measurable_pi_apply q

/-- The complete finite-dimensional law of a selected continuous Brownian
path.  The target measure is mathlib's Brownian projective family, pulled
back along the inclusion of the selected unit-interval times into
nonnegative time. -/
theorem IsBrownianReal.hasLaw_finiteEvaluation_continuousunitIntervalPath
    [MeasurableSpace Ω] {P : Measure Ω} {X : NNReal → Ω → ℝ}
    (hB : IsBrownianReal X P) (hX : ∀ ω, Continuous (X · ω))
    (I : Finset unitInterval) :
    HasLaw
      (ContinuousMap.finiteEvaluation ((↑) : ↑I → unitInterval) ∘
        continuousunitIntervalPath X hX)
      ((BrownianReal.projectiveFamily (I.image unitInterval.toNNReal)).map
        (fun x t ↦ x ⟨unitInterval.toNNReal t,
          Finset.mem_image.2 ⟨t, t.property, rfl⟩⟩)) P := by
  have hMap : HasLaw (unitIntervalFiniteRestriction I)
      ((BrownianReal.projectiveFamily (I.image unitInterval.toNNReal)).map
        (unitIntervalFiniteRestriction I))
      (BrownianReal.projectiveFamily (I.image unitInterval.toNNReal)) :=
    hasLaw_map (measurable_unitIntervalFiniteRestriction I).aemeasurable
  have hLaw := hMap.comp (hB.hasLaw (I.image unitInterval.toNNReal))
  have hRestriction :
      (fun x t ↦ x ⟨unitInterval.toNNReal t,
        Finset.mem_image.2 ⟨t, t.property, rfl⟩⟩) = unitIntervalFiniteRestriction I := rfl
  rw [hRestriction]
  convert hLaw using 1
  funext ω t
  simp [ContinuousMap.finiteEvaluation, unitIntervalFiniteRestriction,
    continuousunitIntervalPath_apply]

/-- The same complete finite-dimensional Brownian law after embedding the
continuous paths into Skorokhod space. -/
theorem IsBrownianReal.hasLaw_finiteEvaluation_cadlagunitIntervalPath
    [MeasurableSpace Ω] {P : Measure Ω} {X : NNReal → Ω → ℝ}
    (hB : IsBrownianReal X P) (hX : ∀ ω, Continuous (X · ω))
    (I : Finset unitInterval) :
    HasLaw
      (fun ω ↦ fun t : ↑I ↦ cadlagunitIntervalPath X hX ω t)
      ((BrownianReal.projectiveFamily (I.image unitInterval.toNNReal)).map
        (fun x t ↦ x ⟨unitInterval.toNNReal t,
          Finset.mem_image.2 ⟨t, t.property, rfl⟩⟩)) P := by
  convert hB.hasLaw_finiteEvaluation_continuousunitIntervalPath hX I using 1
  funext ω t
  simp [ContinuousMap.finiteEvaluation, cadlagunitIntervalPath_apply,
    continuousunitIntervalPath_apply]

end ProbabilityTheory
