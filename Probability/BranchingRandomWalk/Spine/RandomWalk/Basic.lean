/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.EndpointRealization.Field
public import Probability.BranchingRandomWalk.Walk.Basic

/-!
# The spine random walk

The tilted increment product law defines an actual single-root random walk.
Its canonical branching realization has child-slot type `PUnit`, so every
generation contains exactly the unique address `Walk.lineNode n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching.Walk
open ProbabilityTheory.RandomWalk

open Combinatorics.Branching MeasureTheory

/-- The (everywhere-present) random walk supplied by the tilted law in
many-to-one formulas. -/
noncomputable def spineRandomWalk {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) : RandomWalk ℝ ℝ := by
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  exact _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.ofIncrementLaw 0 (tiltedIncrementFieldLaw φ μ)

@[simp] theorem spineRandomWalk_law {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    (spineRandomWalk φ μ hboundary).law =
      (tiltedIncrementFieldLaw φ μ).map (Walk.ofIncrements 0) := by
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  rfl

/-- The spine walk has an everywhere-present increment-path realization. -/
theorem spineRandomWalk_isIncrementPathRealization {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.IsIncrementPathRealization (spineRandomWalk φ μ hboundary) := by
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  exact _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.isIncrementPathRealization_ofIncrementLaw
    0 (tiltedIncrementFieldLaw φ μ)

/-- Boundary normalization makes the spine random walk permanently surviving
almost surely. -/
theorem spineRandomWalk_survivesForever {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.SurvivesForever (spineRandomWalk φ μ hboundary) := by
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    tiltedIncrementFieldLaw_isProbability φ μ hboundary
  exact _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.survivesForever_ofIncrementLaw
    0 (tiltedIncrementFieldLaw φ μ)

/-- The increments in the canonical realization of the spine random walk are
independent. -/
theorem spineRandomWalk_independent {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    iIndepFun (fun n (increment : ℕ → ℝ) => increment n)
      (tiltedIncrementFieldLaw φ μ) :=
  tiltedIncrementFieldLaw_independent φ μ hboundary

/-- Every increment in the canonical spine realization has the tilted
potential law. -/
theorem spineRandomWalk_incrementLaw_coordinate {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) (n : ℕ) :
    (tiltedIncrementFieldLaw φ μ).map (fun increment => increment n) =
      tiltedPotentialLaw φ (-1) μ :=
  tiltedIncrementFieldLaw_coordinate φ μ hboundary n

/-- Weighted many-to-one, together with the random walk whose canonical
increment realization occurs on the right-hand side. -/
theorem weightedEndpointManyToOne_randomWalk
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    weightedBranchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment, f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ :=
  weightedEndpointManyToOne_product d hd potential μ hboundary hf n x

/-- Unweighted many-to-one for the canonical increment realization of the
spine random walk. -/
theorem endpointManyToOne_randomWalk
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    branchingEndpointIterate (potential.comp d hd) μ n f x =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
          f (x + AdditivePath.displacement n increment)
        ∂tiltedIncrementFieldLaw (potential.comp d hd) μ :=
  endpointManyToOne_product d hd potential μ hboundary hf n x

/-- Existential form: the tilted kernel supplies a random walk, and its
canonical increment realization represents the weighted recursion. -/
theorem exists_randomWalk_weightedEndpointManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    {f : ℝ → ENNReal} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    ∃ walk : RandomWalk ℝ ℝ,
      _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.IsIncrementPathRealization walk ∧
      weightedBranchingEndpointIterate (potential.comp d hd) μ n f x =
        ∫⁻ increment, f (x + AdditivePath.displacement n increment)
          ∂tiltedIncrementFieldLaw (potential.comp d hd) μ := by
  refine ⟨spineRandomWalk (potential.comp d hd) μ hboundary,
    spineRandomWalk_isIncrementPathRealization
      (potential.comp d hd) μ hboundary, ?_⟩
  exact weightedEndpointManyToOne_randomWalk
    d hd potential μ hboundary hf n x

end ProbabilityTheory.BranchingRandomWalk.Spine
