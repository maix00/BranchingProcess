/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.SelectedPopulation
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Overflow
import Probability.BranchingRandomWalk.Coupling.Field.Position

/-!
# Coupling first-N selection at different capacities

## Public declarations

- `RootIndexed.selectedPopulationCoupling_of_capacity_le_ae`: if
  $N_1\le N_2$, $N_2>0$, and the first initial cloud embeds into the
  second with positions ordered downwards, both prescribed offspring
  fields have the product marginal law and almost surely the ordered
  embeddings and the minimum order persist at every generation. The first root set has at
  most $N_2$ roots.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The deterministic-initial-configuration comparison of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 3, Lemma 3.9 and Corollary 3.10.
The initial positions use a common label space and may be assigned
independently on disjoint root sets. The same installed field is used for
the whole trajectory. -/
theorem RootIndexed.selectedPopulationCoupling_of_capacity_le_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N₁ N₂ : ℕ) (hN₂ : 0 < N₂) (hcapacity : N₁ ≤ N₂)
    (roots₁ roots₂ : Finset Root) (hroots : roots₁.card ≤ N₂)
    (initialPosition : Root → ℝ)
    (matchRoot : Root → Root)
    (hmatchRoot : Set.MapsTo matchRoot (↑roots₁ : Set Root) ↑roots₂)
    (hinjective : Set.InjOn matchRoot (↑roots₁ : Set Root))
    (horder : ∀ r ∈ roots₁, initialPosition (matchRoot r) ≤ initialPosition r) :
    let selected₁ := fun n field => RootIndexed.selectedPopulationTotalized
      N₁ roots₁ initialPosition id id n (RootIndexed.StepField.left field)
    let V := RootIndexed.restartedRealPositionTrajectoryField
      N₂ roots₂ initialPosition id selected₁
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Root) μ
    Measurable V ∧ P.map V = Q ∧ P.map RootIndexed.StepField.left = Q ∧
    ∀ᵐ field ∂P, ∀ n : ℕ,
      let walk₁ := RootIndexed.BranchingWalk.ofStepField initialPosition
        (RootIndexed.StepField.left field)
      let walk₂ := RootIndexed.BranchingWalk.ofStepField initialPosition (V field)
      let selected₂ := RootIndexed.selectedPopulationTotalized N₂ roots₂
        initialPosition id id n (V field)
      Nonempty (Cloud.SliceDominatingMap id
        (Combinatorics.Branching.Selection.Coupling.populationCloud id walk₁ (selected₁ n field))
        (Combinatorics.Branching.Selection.Coupling.populationCloud id walk₂ selected₂) ()) ∧
      selected₂.inf (fun q => ((walk₂.position id q.1 q.2 : ℝ) : WithTop ℝ)) ≤
        (selected₁ n field).inf (fun p => ((walk₁.position id p.1 p.2 : ℝ) : WithTop ℝ)) := by
  dsimp only
  let population := RootIndexed.nSelectedBRWPopulationTotalizedCausalPopulation
    (Root := Root) (α := α) N₁ roots₁ initialPosition id measurable_id id measurable_id
  let finiteSlices := RootIndexed.nSelectedBRWPopulationTotalizedCausalPopulation_finiteSlices
    (Root := Root) (α := α) N₁ roots₁ initialPosition id measurable_id id measurable_id
  have hslices : finiteSlices.toFinset =
      fun n field => RootIndexed.selectedPopulationTotalized
        N₁ roots₁ initialPosition id id n (RootIndexed.StepField.left field) := by
    funext n field
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  have hinit : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field)) (finiteSlices.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N₂ roots₂
          initialPosition id finiteSlices.toFinset 0 field)) () := by
    intro field
    rw [hslices]
    simp only [RootIndexed.selectedPopulationTotalized,
      RootIndexed.restartedRealPositionNSelectedBRWPopulation]
    refine ⟨fun p => (matchRoot p.1, []), ?_, ?_, ?_⟩
    · intro p hp
      change p ∈ RootIndexed.initialPopulation roots₁ at hp
      obtain ⟨r, hr, rfl⟩ := RootIndexed.mem_initialPopulation_iff.mp hp
      exact RootIndexed.mem_initialPopulation_iff.mpr ⟨matchRoot r, hmatchRoot hr, rfl⟩
    · intro p hp q hq heq
      change p ∈ RootIndexed.initialPopulation roots₁ at hp
      change q ∈ RootIndexed.initialPopulation roots₁ at hq
      obtain ⟨r, hr, rfl⟩ := RootIndexed.mem_initialPopulation_iff.mp hp
      obtain ⟨s, hs, rfl⟩ := RootIndexed.mem_initialPopulation_iff.mp hq
      exact congrArg (fun t => (t, [])) (hinjective hr hs (congrArg Prod.fst heq))
    · intro p hp
      change p ∈ RootIndexed.initialPopulation roots₁ at hp
      obtain ⟨r, hr, rfl⟩ := RootIndexed.mem_initialPopulation_iff.mp hp
      change RootIndexed.position initialPosition id (RootIndexed.StepField.right field)
          (matchRoot r) [] ≤
        RootIndexed.position initialPosition id (RootIndexed.StepField.left field) r []
      simpa [RootIndexed.position] using horder r hr
  obtain ⟨hm, hlaw, hleft, _, hcompare⟩ :=
    RootIndexed.restartedRealPositionComparison_throughOverflow_ae
      μ hnorm N₂ hN₂ roots₂ initialPosition population finiteSlices hinit
  refine ⟨?_, ?_, hleft, ?_⟩
  · simpa only [hslices] using hm
  · simpa only [hslices] using hlaw
  filter_upwards [hcompare] with field hcompare
  intro n
  have hbefore : (n : WithTop ℕ) < finsetPopulationOverflowTime finiteSlices.toFinset N₂ field := by
    apply lt_of_not_ge
    intro hover
    obtain ⟨k, _, hk⟩ := (finsetPopulationOverflowTime_le_iff _ _ _ _).1 hover
    rw [hslices] at hk
    cases k with
    | zero =>
      exact (not_lt_of_ge (by simpa [RootIndexed.selectedPopulationTotalized,
        RootIndexed.initialPopulation_card] using hroots)) hk
    | succ k =>
      exact (not_lt_of_ge ((RootIndexed.selectedPopulationTotalized_card_le N₁ roots₁
        initialPosition id id k (RootIndexed.StepField.left field)).trans hcapacity)) hk
  exact ⟨by simpa only [hslices] using (hcompare n).1 hbefore,
    by simpa only [hslices] using (hcompare n).2 hbefore.le⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
