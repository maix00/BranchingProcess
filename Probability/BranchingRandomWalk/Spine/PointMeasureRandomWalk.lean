/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.PointMeasureEndpoint
public import Probability.BranchingRandomWalk.Spine.EndpointRealization.Independent
public import Probability.BranchingRandomWalk.Walk.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration

/-!
# Spine random walk from a random-measure offspring law

Boundary normalization turns the enumeration-free tilted law into a
probability law.  Its countable product supplies the independent increments
of the spine random walk used by the many-to-one formula.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching.Walk

/-- Independent increment field with the enumeration-free tilted marginal. -/
noncomputable def pointMeasureIncrementLaw
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E)) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ =>
    PointProcess.tiltedLaw potential (-1) law

theorem pointMeasureIncrementLaw_eq_independentIncrementLaw
    {E : Type*} [MeasurableSpace E]
    (potential : E → ℝ) (law : Measure (Measure E)) :
    pointMeasureIncrementLaw potential law =
      RandomWalk.independentIncrementLaw
        (PointProcess.tiltedLaw potential (-1) law) := rfl

theorem pointMeasureIncrementLaw_isProbability
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    IsProbabilityMeasure (pointMeasureIncrementLaw potential law) := by
  let _ : IsProbabilityMeasure
      (PointProcess.tiltedLaw potential (-1) law) :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  unfold pointMeasureIncrementLaw
  infer_instance

theorem pointMeasureIncrementLaw_coordinate
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    (n : ℕ) :
    (pointMeasureIncrementLaw potential law).map (fun increment => increment n) =
      PointProcess.tiltedLaw potential (-1) law := by
  let _ : IsProbabilityMeasure
      (PointProcess.tiltedLaw potential (-1) law) :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  unfold pointMeasureIncrementLaw
  exact Measure.infinitePi_map_eval
    (fun _ : ℕ => PointProcess.tiltedLaw potential (-1) law) n

theorem pointMeasureIncrementLaw_independent
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (pointMeasureIncrementLaw potential law) := by
  let _ : IsProbabilityMeasure
      (PointProcess.tiltedLaw potential (-1) law) :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  unfold pointMeasureIncrementLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => PointProcess.tiltedLaw potential (-1) law)
    (X := fun _ : ℕ => id) (fun _ => measurable_id))

/-- The everywhere-present random walk canonically supplied by an
offspring random-measure law. -/
noncomputable def pointMeasureSpineRandomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    RandomWalk ℝ ℝ := by
  let _ : IsProbabilityMeasure (pointMeasureIncrementLaw potential law) :=
    pointMeasureIncrementLaw_isProbability hpotential law hnormalization
  exact RandomWalk.ofIncrementLaw 0 (pointMeasureIncrementLaw potential law)

@[simp] theorem pointMeasureSpineRandomWalk_law
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    (pointMeasureSpineRandomWalk hpotential law hnormalization).law =
      (pointMeasureIncrementLaw potential law).map
        (ofIncrements 0) := by
  let _ : IsProbabilityMeasure (pointMeasureIncrementLaw potential law) :=
    pointMeasureIncrementLaw_isProbability hpotential law hnormalization
  rfl

theorem pointMeasureSpineRandomWalk_isIncrementPathRealization
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    RandomWalk.IsIncrementPathRealization
      (pointMeasureSpineRandomWalk hpotential law hnormalization) := by
  let _ : IsProbabilityMeasure (pointMeasureIncrementLaw potential law) :=
    pointMeasureIncrementLaw_isProbability hpotential law hnormalization
  exact RandomWalk.isIncrementPathRealization_ofIncrementLaw
    0 (pointMeasureIncrementLaw potential law)

theorem pointMeasureSpineRandomWalk_survivesForever
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    RandomWalk.SurvivesForever
      (pointMeasureSpineRandomWalk hpotential law hnormalization) := by
  let _ : IsProbabilityMeasure (pointMeasureIncrementLaw potential law) :=
    pointMeasureIncrementLaw_isProbability hpotential law hnormalization
  exact RandomWalk.survivesForever_ofIncrementLaw
    0 (pointMeasureIncrementLaw potential law)

theorem pointMeasureSpineRandomWalk_independent
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (pointMeasureIncrementLaw potential law) :=
  pointMeasureIncrementLaw_independent hpotential law hnormalization

/-- The enumeration-free weighted generation recursion is represented by the
increment realization of the constructed spine random walk. -/
theorem pointMeasureWeightedEndpointManyToOne_randomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    pointMeasureWeightedEndpointIterate potential (-1) law n f x =
      ∫⁻ increment, f (x + partialSum n increment)
        ∂pointMeasureIncrementLaw potential law := by
  let ν := PointProcess.tiltedLaw potential (-1) law
  let _ : IsProbabilityMeasure ν :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  rw [pointMeasureWeightedEndpointManyToOne hpotential (-1) law
    hnormalization hf n]
  rw [pointMeasureIncrementLaw_eq_independentIncrementLaw]
  exact (lintegral_independentPosition_eq_iterate ν hf n x).symm

/-- The enumeration-free unweighted generation recursion is represented by
the same spine increment realization with the reciprocal terminal weight. -/
theorem pointMeasureEndpointManyToOne_randomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    pointMeasureEndpointIterate potential law n f x =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (partialSum n increment)) *
          f (x + partialSum n increment)
        ∂pointMeasureIncrementLaw potential law := by
  let ν := PointProcess.tiltedLaw potential (-1) law
  let _ : IsProbabilityMeasure ν :=
    PointProcess.tiltedLaw_isProbability hpotential (-1) law hnormalization
  rw [pointMeasureEndpointManyToOne hpotential law hnormalization hf n]
  rw [pointMeasureIncrementLaw_eq_independentIncrementLaw]
  exact (lintegral_independentPosition_untilted_eq_iterate ν hf n x).symm

/-- Existential many-to-one statement: a spine random walk exists for every
normalized offspring random-measure law. -/
theorem exists_pointMeasureSpineRandomWalk
    {E : Type*} [MeasurableSpace E]
    {potential : E → ℝ} (hpotential : Measurable potential)
    (law : Measure (Measure E))
    (hnormalization : PointProcess.HasNormalization potential (-1) law)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    ∃ walk : RandomWalk ℝ ℝ,
      RandomWalk.IsIncrementPathRealization walk ∧
      pointMeasureWeightedEndpointIterate potential (-1) law n f x =
        ∫⁻ increment, f (x + partialSum n increment)
          ∂pointMeasureIncrementLaw potential law := by
  refine ⟨pointMeasureSpineRandomWalk hpotential law hnormalization,
    pointMeasureSpineRandomWalk_isIncrementPathRealization
      hpotential law hnormalization, ?_⟩
  exact pointMeasureWeightedEndpointManyToOne_randomWalk
    hpotential law hnormalization hf n x

end ProbabilityTheory.BranchingRandomWalk.Spine
