/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Population
public import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
public import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition.Real
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
/-!
# Restarted selected BRW population for the second stage

## Public declarations

Write \(P\) for the restarted selected BRW population. Every generation slice is
finite for each restarted field:

\[
\forall n,\omega,\qquad
P_n(\omega)\text{ is finite}.
\]

`positiveASelectedBRWPopulation m ell ellN logN b v c kappa` is the causal
population on `RestartedField m` with initial roots `Fin m`, cutoff `ell`,
and the restarted corridor window determined by `ellN`, `logN`, `b`, `v`,
`c`, and `kappa`. Its generation-`n` slice is finite for every field, as
stated by `positiveASelectedBRWPopulation_finiteSlices`. This is the population
input to the second-stage root selection in Chapter 3, Lemma 3.5 of WANG
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

@[expose] public section

/-- The selected BRW population used in the two-stage positive-`a` argument. -/
noncomputable def positiveASelectedBRWPopulation
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)] :
    RestartedPopulation m := by
  let initial := RootIndexed.initialPopulation (α := ℕ)
    (Finset.univ : Finset (Fin m))
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨r, _hr, rfl⟩
    simp
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    (positiveARestartedWindow ell ellN logN b v c κ)
    (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    (positiveAWindowUpper ell ellN logN b v c κ)
    (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)

theorem positiveASelectedBRWPopulation_finiteSlices
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)] :
    (positiveASelectedBRWPopulation m ell ellN logN b v c κ).FiniteSlices := by
  classical
  dsimp [positiveASelectedBRWPopulation]
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
    (fun _ : Fin m => 0) id measurable_id
    (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
    (by simp [RootIndexed.mem_initialPopulation_iff]) ell
    (positiveARestartedWindow ell ellN logN b v c κ)
    (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    (positiveAWindowUpper ell ellN logN b v c κ)
    (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)


end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
