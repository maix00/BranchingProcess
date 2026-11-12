/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.SelectedPopulation
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
public import Probability.BranchingRandomWalk.Coupling.Field.Position

/-!
# Coupling first-`N` BRW populations from nested root sets

For root sets \(R_0\subseteq R_1\), the first-\(N\) BRW population from
\(R_0\) is causal and has at most \(N\) particles at each positive
generation.  Rank installation couples it with first-\(N\) selection from
\(R_1\).


## Public declarations

If \(R_0\subseteq R_1\), then boundary normalization gives a
slice-dominating injection from the first-\(N\) BRW population rooted at
\(R_0\) into the one rooted at \(R_1\), almost surely at every generation:

\[
R_0\subseteq R_1
\Longrightarrow
\forall n,\quad
\mathbb P\!\left(
  \exists\,\iota_n:P_n(R_0)
    \hookrightarrow P_n(R_1),\
  \phi(X_n^{R_1}(\iota_n(p)))
    \le\phi(X_n^{R_0}(p))\ \forall p
\right)=1.
\]

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.selectedPopulationNestedRootsCoupledInjection_ae`:
  if `subsetBRWRoots ⊆ supersetBRWRoots`, then almost surely each generation
  slice of the first-`N` BRW rooted at `subsetBRWRoots` injects into the
  rank-installed first-`N` BRW rooted at `supersetBRWRoots`, under boundary
  normalization of the offspring law.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- First-`N` selection from a subset of BRW roots admits an almost-sure
rank-installed injection into first-`N` selection from the containing root
set.  Boundary normalization supplies admissibility for the first-`N`
selector on that larger root set. -/
theorem RootIndexed.selectedPopulationNestedRootsCoupledInjection_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (subsetBRWRoots supersetBRWRoots : Finset Root)
    (hroots : subsetBRWRoots ⊆ supersetBRWRoots)
    (initialPosition : Root → ℝ) (n : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      Nonempty (Cloud.SliceDominatingMap id
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field))
          (RootIndexed.selectedPopulationTotalized N subsetBRWRoots initialPosition
            id id n (RootIndexed.StepField.left field)))
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.restartedRealPositionNSelectedBRWField N supersetBRWRoots
              initialPosition id
              (fun k field => RootIndexed.selectedPopulationTotalized N
                subsetBRWRoots initialPosition id id k
                (RootIndexed.StepField.left field)) n field))
          (RootIndexed.restartedRealPositionNSelectedBRWPopulation N supersetBRWRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N
              subsetBRWRoots initialPosition id id k
              (RootIndexed.StepField.left field)) n field)) ()) := by
  let subsetNSelectedBRWPopulation := RootIndexed.nSelectedBRWPopulationTotalizedCausalPopulation
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N subsetBRWRoots initialPosition id measurable_id id measurable_id
  let hsubsetNSelectedBRWPopulationFiniteSlices := RootIndexed.nSelectedBRWPopulationTotalizedCausalPopulation_finiteSlices
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N subsetBRWRoots initialPosition id measurable_id id measurable_id
  have hsubsetNSelectedBRWPopulationEq : hsubsetNSelectedBRWPopulationFiniteSlices.toFinset =
      (fun k field => RootIndexed.selectedPopulationTotalized N subsetBRWRoots
        initialPosition id id k (RootIndexed.StepField.left field)) := by
    funext k
    funext field
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    change (subsetNSelectedBRWPopulation.toPopulation field).particles k = _
    rfl
  have hinitial : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hsubsetNSelectedBRWPopulationFiniteSlices.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N supersetBRWRoots
          initialPosition id (hsubsetNSelectedBRWPopulationFiniteSlices.toFinset) 0 field)) () := by
    intro field
    have hzero : hsubsetNSelectedBRWPopulationFiniteSlices.toFinset 0 field =
        RootIndexed.initialPopulation (α := α) subsetBRWRoots := by
      apply Finset.coe_injective
      rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
      change (subsetNSelectedBRWPopulation.toPopulation field).particles 0 = _
      simp [subsetNSelectedBRWPopulation, RootIndexed.nSelectedBRWPopulationTotalizedCausalPopulation,
        RootIndexed.selectedPopulationTotalized]
    rw [hzero]
    simpa [RootIndexed.restartedRealPositionNSelectedBRWPopulation,
      RootIndexed.restartedRealPositionNSelectedBRWField,
      RootIndexed.selectedPopulationTotalized] using
      (ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.initialPopulationSliceDominatingMap_of_subset
        (α := α) (Mark := ℝ) id id initialPosition subsetBRWRoots supersetBRWRoots
        hroots (RootIndexed.StepField.left field) (RootIndexed.StepField.right field))
  have hgeneric := RootIndexed.restartedRealPositionCoupledInjection_ae
    μ hnorm N supersetBRWRoots initialPosition subsetNSelectedBRWPopulation hsubsetNSelectedBRWPopulationFiniteSlices hinitial n
  filter_upwards [hgeneric] with field hgood
  have hcapacity : ∀ k < n, (hsubsetNSelectedBRWPopulationFiniteSlices.toFinset (k + 1) field).card ≤ N := by
    intro k hk
    have hcard := RootIndexed.selectedPopulationTotalized_card_le
      N subsetBRWRoots initialPosition id id k (RootIndexed.StepField.left field)
    simpa [hsubsetNSelectedBRWPopulationEq] using hcard
  have hmap := hgood hcapacity
  simpa only [hsubsetNSelectedBRWPopulationEq] using hmap

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
