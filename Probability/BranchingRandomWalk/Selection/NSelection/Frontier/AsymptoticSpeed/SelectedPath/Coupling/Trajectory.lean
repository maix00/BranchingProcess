/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Overflow

/-!
# Coupling the entire selected-path trajectory

## Public declarations

- `Coupling.selectedToNSelectedBRWTrajectory_ae`: if every concurrent
  growth-trial slice is bounded by $1+(d+1)(2c)\le N$, the first-$N$
  field has the offspring product law and, almost surely, every selected-path
  slice $P_n$ embeds into its first-$N$ counterpart $Q_n$ with
  $x_{Q_n}(\iota_n(p))\le x_{P_n}(p)$.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath

open Combinatorics.UlamHarris Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- Apply the stopped comparison of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.15, to the capped selected-path population used for the
single-particle initial condition in Theorem 1.1. The deterministic
concurrent-trial capacity bound makes the overflow time infinite. -/
theorem Coupling.selectedToNSelectedBRWTrajectory_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (cap duration : ℕ) (hbounded : growth.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (hcapacity : 1 + (duration + 1) * (2 * cap) ≤ N)
    (r : Root) :
    let slices := (Population.leftBRWFamily_finiteSlices R growth hR
      hgrowth cap duration r).toFinset
    let V := RootIndexed.restartedRealPositionTrajectoryField N {r} initialPosition id slices
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    Measurable V ∧ P.map V = RootIndexed.stepFieldLaw (Root := Root) μ ∧
    ∀ᵐ field ∂P, ∀ n : ℕ,
      Nonempty (Cloud.SliceDominatingMap id
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field)) (slices n field))
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition (V field))
          (RootIndexed.selectedPopulationTotalized N {r} initialPosition id id n (V field))) ()) := by
  dsimp only
  have hN : 0 < N := by omega
  obtain ⟨hm, hlaw, _, _, hcomp⟩ :=
    RootIndexed.restartedRealPositionComparison_throughOverflow_ae μ N hN {r} initialPosition
      (RootIndexed.selectedPopulationTotalized_admissible_ae μ hnorm N {r} initialPosition)
      (Population.leftBRWFamily R growth hR hgrowth cap duration r)
      (Population.leftBRWFamily_finiteSlices R growth hR hgrowth cap duration r)
      (Population.leftBRWFamily_initialInjection R growth hR hgrowth cap duration r N initialPosition)
  refine ⟨hm, hlaw, ?_⟩
  filter_upwards [hcomp] with field hcomp
  intro n
  apply (hcomp n).1
  apply lt_of_not_ge
  intro hover
  obtain ⟨k, _, hk⟩ := (finsetPopulationOverflowTime_le_iff _ N n field).mp hover
  have hcard := Population.leftBRWFamily_card_le R growth hR hgrowth
    cap duration hbounded hcap r k field
  exact (not_lt_of_ge (hcard.trans hcapacity)) hk

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath

end
