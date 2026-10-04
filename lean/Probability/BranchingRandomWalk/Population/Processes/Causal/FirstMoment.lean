/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity
import Probability.BranchingRandomWalk.Population.Processes.Causal.PathBound
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.FiniteExpectations
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne

/-!
# First moments of causal killed populations

The pathwise bounds are integrated under the root-indexed field law and then
reduced to one-dimensional spine expectations.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching.Walk
namespace RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Spine

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The first moment of a one-root restarted killed generation is bounded by
the corresponding spine path expectation.  This theorem contains no second
moment or pair estimate. -/
theorem lintegral_size_le_spine_restartedWindow
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (r : Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d)
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (⟨d, hd⟩ : Potential Mark) μ)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (hzero : 0 ∈ window 0)
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (n : ℕ) :
    let P := ofRestartedRealPositionSets initialPosition d hd
      ({(r, ([] : TreeNode α))} : Finset (RootIndexed.TreeNode Root α))
      (by simp) cutoff window hwindow upper hupper
    (∫⁻ field, P.size n field
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (partialSum n increment)) *
          restartedWindowTest cutoff window
            (history n (initialPosition r) increment)
        ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ := by
  dsimp only
  let test : (Fin (n + 1) → ℝ) → ENNReal :=
    restartedWindowTest cutoff window
  have htest : Measurable test :=
    restartedWindowTest_measurable cutoff window hwindow
  calc
    (∫⁻ field,
        (ofRestartedRealPositionSets initialPosition d hd
          ({(r, ([] : TreeNode α))} :
            Finset (RootIndexed.TreeNode Root α))
          (by simp) cutoff window hwindow upper hupper).size n field
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
        ∫⁻ field,
          pathGeneration (⟨d, hd⟩ : Potential Mark) n test
            (initialPosition r) (field r)
          ∂RootIndexed.stepFieldLaw (Root := Root) μ :=
      lintegral_mono fun field =>
        size_le_pathGeneration_restartedWindow r initialPosition d hd cutoff
          window hwindow hzero upper hupper n field
    _ = ∫⁻ tree : Combinatorics.Branching.StepField α Mark,
          pathGeneration (⟨d, hd⟩ : Potential Mark) n test
            (initialPosition r) tree
          ∂ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ := by
      exact RootIndexed.lintegral_root_observable μ r _
        (pathGeneration_measurable (⟨d, hd⟩ : Potential Mark) n htest
          (initialPosition r))
    _ = ∫⁻ increment,
        ENNReal.ofReal (Real.exp (partialSum n increment)) *
          test (history n (initialPosition r) increment)
        ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ :=
      pathManyToOneCore (⟨d, hd⟩ : Potential Mark) μ hboundary n htest
        (initialPosition r)

/-- The finite-root killed population needs only the sum of the corresponding
one-dimensional spine expectations.  No independence between the summands
is used in this first-moment estimate. -/
theorem lintegral_size_le_sum_spine_restartedWindow
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (roots : Finset Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d)
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (⟨d, hd⟩ : Potential Mark) μ)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (hzero : 0 ∈ window 0)
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (n : ℕ) :
    let P := ofRestartedRealPositionSets initialPosition d hd
      (RootIndexed.initialPopulation (α := α) roots)
      (by simp [RootIndexed.mem_initialPopulation_iff])
      cutoff window hwindow upper hupper
    (∫⁻ field, P.size n field
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
      ∑ r ∈ roots, ∫⁻ increment,
        ENNReal.ofReal (Real.exp (partialSum n increment)) *
          restartedWindowTest cutoff window
            (history n (initialPosition r) increment)
        ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ := by
  dsimp only
  let test : (Fin (n + 1) → ℝ) → ENNReal :=
    restartedWindowTest cutoff window
  have htest : Measurable test :=
    restartedWindowTest_measurable cutoff window hwindow
  calc
    (∫⁻ field,
        (ofRestartedRealPositionSets initialPosition d hd
          (RootIndexed.initialPopulation (α := α) roots)
          (by simp [RootIndexed.mem_initialPopulation_iff])
          cutoff window hwindow upper hupper).size n field
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
        ∫⁻ field, ∑ r ∈ roots,
          pathGeneration (⟨d, hd⟩ : Potential Mark) n test
            (initialPosition r) (field r)
          ∂RootIndexed.stepFieldLaw (Root := Root) μ :=
      lintegral_mono fun field =>
        size_le_sum_pathGeneration_restartedWindow roots initialPosition d hd
          cutoff window hwindow hzero upper hupper n field
    _ = ∑ r ∈ roots,
        ∫⁻ tree : Combinatorics.Branching.StepField α Mark,
          pathGeneration (⟨d, hd⟩ : Potential Mark) n test
            (initialPosition r) tree
          ∂ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ := by
      exact RootIndexed.lintegral_finset_root_observables μ roots
        (fun r tree => pathGeneration (⟨d, hd⟩ : Potential Mark) n test
          (initialPosition r) tree)
        (fun r _ => pathGeneration_measurable
          (⟨d, hd⟩ : Potential Mark) n htest (initialPosition r))
    _ = ∑ r ∈ roots, ∫⁻ increment,
        ENNReal.ofReal (Real.exp (partialSum n increment)) *
          test (history n (initialPosition r) increment)
        ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ := by
      apply Finset.sum_congr rfl
      intro r _
      exact pathManyToOneCore (⟨d, hd⟩ : Potential Mark) μ hboundary n htest
        (initialPosition r)

end RootIndexed.CausalPopulation
end ProbabilityTheory.BranchingRandomWalk
