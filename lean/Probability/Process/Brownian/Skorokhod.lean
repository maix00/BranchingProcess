/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.UnitInterval
public import Probability.Process.Path.UnitInterval
public import Probability.Process.Path.Skorokhod
public import Probability.Process.Path.FiniteDimensional
public import Topology.Cadlag.Skorokhod.ContinuousMap

/-!
# Brownian processes in Skorokhod space

This file maps any chosen everywhere-continuous, coordinate-measurable version
of a real process to the Skorokhod path space on `[0, 1]`. In particular it
applies to such a version of any process satisfying mathlib's
`IsBrownianReal` predicate. It does not depend on a particular construction
of Brownian motion.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- A chosen continuous measurable version of a Brownian process has the
abstract Skorokhod path law above. -/
theorem IsBrownianReal.hasLaw_cadlagunitIntervalPath [MeasurableSpace Ω]
    {P : Measure Ω} {X : NNReal → Ω → ℝ} (_hB : IsBrownianReal X P)
    (hX : ∀ ω, Continuous (X · ω))
    (hXmeas : ∀ t, Measurable (X t)) :
    HasLaw (cadlagunitIntervalPath X hX)
      (cadlagunitIntervalPathLaw P X hX hXmeas) P :=
  ProbabilityTheory.hasLaw_cadlagunitIntervalPath P X hX hXmeas

/-- Every evaluation of a selected continuous Brownian path on the unit
interval has the Gaussian marginal prescribed by mathlib's Brownian
predicate.  This is the one-dimensional marginal interface used when a
functional limit theorem targets the bundled continuous path. -/
theorem IsBrownianReal.hasLaw_continuousunitIntervalPath_apply
    [MeasurableSpace Ω] {P : Measure Ω} {X : NNReal → Ω → ℝ}
    (hB : IsBrownianReal X P) (hX : ∀ ω, Continuous (X · ω))
    (t : unitInterval) :
    HasLaw (fun ω => continuousunitIntervalPath X hX ω t)
      (gaussianReal 0 (unitIntervalToNNReal t)) P := by
  simpa only [continuousunitIntervalPath_apply] using
    hB.hasLaw_eval (unitIntervalToNNReal t)

/-- The same Brownian marginal law after embedding the selected path into
Skorokhod space. -/
theorem IsBrownianReal.hasLaw_cadlagunitIntervalPath_apply
    [MeasurableSpace Ω] {P : Measure Ω} {X : NNReal → Ω → ℝ}
    (hB : IsBrownianReal X P) (hX : ∀ ω, Continuous (X · ω))
    (t : unitInterval) :
    HasLaw (fun ω => cadlagunitIntervalPath X hX ω t)
      (gaussianReal 0 (unitIntervalToNNReal t)) P := by
  simpa only [cadlagunitIntervalPath_apply] using
    hB.hasLaw_eval (unitIntervalToNNReal t)

/-- Pull a vector indexed by the image of a finite family of unit-interval
times back to the original family. -/
def unitIntervalFiniteRestriction
    (I : Finset unitInterval) :
    (↑(I.image unitIntervalToNNReal) → ℝ) → (↑I → ℝ) :=
  fun x t ↦ x ⟨unitIntervalToNNReal t,
    Finset.mem_image.2 ⟨t, t.property, rfl⟩⟩

theorem measurable_unitIntervalFiniteRestriction
    (I : Finset unitInterval) :
    Measurable (unitIntervalFiniteRestriction I) := by
  apply Measurable.of_eval
  intro t
  let q : ↑(I.image unitIntervalToNNReal) :=
    ⟨unitIntervalToNNReal t, Finset.mem_image.2 ⟨t, t.property, rfl⟩⟩
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
      (Process.Path.finiteEvaluation ((↑) : ↑I → unitInterval) ∘
        continuousunitIntervalPath X hX)
      ((BrownianReal.projectiveFamily (I.image unitIntervalToNNReal)).map
        (unitIntervalFiniteRestriction I)) P := by
  have hMap : HasLaw (unitIntervalFiniteRestriction I)
      ((BrownianReal.projectiveFamily (I.image unitIntervalToNNReal)).map
        (unitIntervalFiniteRestriction I))
      (BrownianReal.projectiveFamily (I.image unitIntervalToNNReal)) :=
    hasLaw_map (measurable_unitIntervalFiniteRestriction I).aemeasurable
  have hLaw := hMap.comp (hB.hasLaw (I.image unitIntervalToNNReal))
  convert hLaw using 1
  funext ω t
  simp [Process.Path.finiteEvaluation, unitIntervalFiniteRestriction,
    continuousunitIntervalPath_apply]

/-- The same complete finite-dimensional Brownian law after embedding the
continuous paths into Skorokhod space. -/
theorem IsBrownianReal.hasLaw_finiteEvaluation_cadlagunitIntervalPath
    [MeasurableSpace Ω] {P : Measure Ω} {X : NNReal → Ω → ℝ}
    (hB : IsBrownianReal X P) (hX : ∀ ω, Continuous (X · ω))
    (I : Finset unitInterval) :
    HasLaw
      (fun ω ↦ fun t : ↑I ↦ cadlagunitIntervalPath X hX ω t)
      ((BrownianReal.projectiveFamily (I.image unitIntervalToNNReal)).map
        (unitIntervalFiniteRestriction I)) P := by
  convert hB.hasLaw_finiteEvaluation_continuousunitIntervalPath hX I using 1
  funext ω t
  simp [Process.Path.finiteEvaluation, cadlagunitIntervalPath_apply,
    continuousunitIntervalPath_apply]

end ProbabilityTheory
