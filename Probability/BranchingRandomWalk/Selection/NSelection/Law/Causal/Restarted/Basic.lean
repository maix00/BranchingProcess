/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Offspring

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Basic
public import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition.Real
public import Probability.BranchingRandomWalk.Population.Processes.Selected.GenerationUpdate
import Probability.BranchingRandomWalk.Coupling.Field.Position

/-!
# Restarted real-position source and matched target

## Public declarations

- `RootIndexed.restartedRealPositionSource` is the causal population on the left
  coordinate of a two-copy step field, killed by the restarted real-position
  windows.
- `RootIndexed.restartedRealPositionSource_finiteSlices` proves every slice is
  finite, and `restartedRealPositionSourceSlice` represents its slice by a
  `Finset`.
- `RootIndexed.restartedRealPositionMatchedField` recursively installs source
  steps at equal-rank particles of the totalized first-`N` target; its value at
  stage `n` is a step field on the original root set.
- `RootIndexed.restartedRealPositionMatchedPopulation` evaluates the
  totalized first-`N` population on that matched field at generation `n`.

Writing \(S_n(\omega)\) for the finite restarted-source slice,
\(V_n(\omega)\) for the matched field at stage \(n\), and \(T_n(\omega)\)
for the selected target population, the definitions give

\[
  S_n(\omega) = \operatorname{FiniteSlices.toFinset}(n,\omega), \qquad
  T_n(\omega) = \operatorname{SelectedPopulationTotalized}(N,V_n(\omega)).
\]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The restarted killed population, realized on the left half of the common
two-copy pre-sampled field used by rank installation. -/
noncomputable def RootIndexed.restartedRealPositionSource
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k)) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left := by
  let killed := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
  have hleft : ∀ k, @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α Mark)
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) k)
      RootIndexed.StepField.left := by
    intro k
    rw [show RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α Mark →
          RootIndexed.StepField Root α Mark) by rfl]
    exact RootIndexed.StepField.reindex_filtration_measurable
      (X := Mark) Sum.inl k
  exact killed.pullback RootIndexed.StepField.left
    hleft
    (by rfl)

theorem RootIndexed.restartedRealPositionSource_finiteSlices
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k)) :
    (RootIndexed.restartedRealPositionSource initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper).FiniteSlices := by
  intro n field
  unfold RootIndexed.restartedRealPositionSource
  rw [RootIndexed.CausalPopulation.pullback_population]
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
    n (RootIndexed.StepField.left field)

/-- The finite presentation of one killed source slice used by the concrete
first-`N` coupling algorithm.  Finiteness remains a theorem about the
set-valued source rather than part of the population type. -/
noncomputable def RootIndexed.restartedRealPositionSourceSlice
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    Finset (RootIndexed.TreeNode Root α) :=
  (RootIndexed.restartedRealPositionSource_finiteSlices initialPosition d hd
    initial hinitialDepth cutoff window hwindow upper hupper).toFinset n field

/-- The finite rank-installed target field for a restarted source. The target
population uses the totalized selector, so this construction is defined even
on raw fields where a first-`N` segment does not exist. -/
noncomputable def RootIndexed.restartedRealPositionMatchedField
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α)) :
    ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark :=
  RootIndexed.rankInstalledField
    (fun k field p => RootIndexed.observedPositionAtGeneration initialPosition d id k
      (RootIndexed.StepField.left field) p)
    (fun k _ field p => RootIndexed.observedPositionAtGeneration initialPosition d id k
      field p)
    source
    (fun k _ field => RootIndexed.selectedPopulationTotalized N roots
      initialPosition d id k field)
    RootIndexed.StepField.left RootIndexed.StepField.right

/-- The first-`N` target population evaluated on its finite rank-installed
field. -/
noncomputable def RootIndexed.restartedRealPositionMatchedPopulation
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    Finset (RootIndexed.TreeNode Root α) :=
  RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
    (RootIndexed.restartedRealPositionMatchedField N roots initialPosition d
      source n field)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
