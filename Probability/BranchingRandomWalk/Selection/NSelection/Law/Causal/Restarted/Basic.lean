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
# Restarted real-position selected population and its first-\(N\) coupling

## Public declarations

- `RootIndexed.restartedRealPositionSelectedBRWPopulation` is the causal BRW population selected on the left coordinate of a two-copy
  step field by the restarted real-position windows.
- `RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices` proves every slice is
  finite, and `restartedRealPositionSelectedBRWPopulationSlice` represents its slice by a
  `Finset`.
- `RootIndexed.restartedRealPositionNSelectedBRWField` recursively installs the
  selected population's steps at equal-rank particles of the totalized
  first-`N` population; its value at
  stage `n` is a step field on the original root set.
- `RootIndexed.restartedRealPositionNSelectedBRWPopulation` evaluates the
  totalized first-`N` population on that matched field at generation `n`.

Write \(P_n(\omega)\) for the finite restarted selected-population slice,
\(V_n(\omega)\) for the matched field at stage \(n\), and
\(P_n^{(N)}(\omega)\) for the first-\(N\) population.  The definitions give

\[
  P_n(\omega) = \operatorname{FiniteSlices.toFinset}(n,\omega), \qquad
  P_n^{(N)}(\omega) = \operatorname{SelectedPopulationTotalized}(N,V_n(\omega)).
\]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The restarted selected BRW population, realized on the left half of the
common two-copy pre-sampled field used by rank installation. -/
noncomputable def RootIndexed.restartedRealPositionSelectedBRWPopulation
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
  let selectedBRWPopulation := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
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
  exact selectedBRWPopulation.pullback RootIndexed.StepField.left
    hleft
    (by rfl)

theorem RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k)) :
    (RootIndexed.restartedRealPositionSelectedBRWPopulation initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper).FiniteSlices := by
  intro n field
  unfold RootIndexed.restartedRealPositionSelectedBRWPopulation
  rw [RootIndexed.CausalPopulation.pullback_population]
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
    n (RootIndexed.StepField.left field)

/-- The finite presentation of one restarted selected BRW slice used by the
concrete first-`N` coupling algorithm. Finiteness remains a theorem about the
set-valued BRW population rather than part of the population type. -/
noncomputable def RootIndexed.restartedRealPositionSelectedBRWPopulationSlice
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
  (RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices initialPosition d hd
    initial hinitialDepth cutoff window hwindow upper hupper).toFinset n field

/-- The finite rank-installed field for a restarted selected population.  The
first-`N` population uses the totalized selector, so this construction is defined even
on raw fields where a first-`N` segment does not exist. -/
noncomputable def RootIndexed.restartedRealPositionNSelectedBRWField
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α)) :
    ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark :=
  RootIndexed.rankInstalledField
    (fun k field p => RootIndexed.observedPositionAtGeneration initialPosition d id k
      (RootIndexed.StepField.left field) p)
    (fun k _ field p => RootIndexed.observedPositionAtGeneration initialPosition d id k
      field p)
    selectedBRWPopulation
    (fun k _ field => RootIndexed.selectedPopulationTotalized N roots
      initialPosition d id k field)
    RootIndexed.StepField.left RootIndexed.StepField.right

/-- The first-`N` population evaluated on its finite rank-installed field. -/
noncomputable def RootIndexed.restartedRealPositionNSelectedBRWPopulation
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    Finset (RootIndexed.TreeNode Root α) :=
  RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
    (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition d
      selectedBRWPopulation n field)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
