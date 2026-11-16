/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Basic

/-!
# A single field for the installed trajectory

## Public declarations

- `RootIndexed.restartedRealPositionTrajectoryField` sets
  $V(r,u)=V_{|u|+1}(r,u)$, where $V_j$ is the stage-$j$ installed field.
- `RootIndexed.restartedRealPositionTrajectoryField_eq_stage` gives
  $V(r,u)=V_n(r,u)$ for $|u|<n$.
- `RootIndexed.restartedRealPositionTrajectoryField_measurable_law`
  gives measurability and the product-field marginal $P\circ V^{-1}=Q$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- Assemble the consistent rank-installed stages into one field by reading
each address at the stage immediately after its mark was installed. -/
noncomputable def RootIndexed.restartedRealPositionTrajectoryField
    {Root α Mark : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (population : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α Mark) : RootIndexed.StepField Root α Mark :=
  fun r u => RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition d
    population (u.length + 1) field r u

theorem RootIndexed.restartedRealPositionTrajectoryField_eq_stage
    {Root α Mark : Type*} [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (population : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (n : ℕ) (r : Root) (u : TreeNode α) (hu : u.length < n) :
    RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition d population field r u =
      RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition d
        population n field r u := by
  symm
  exact RootIndexed.rankInstalledField_apply_stable _ _ _ _ _ _ field r u
    (Nat.succ_le_of_lt hu) (Nat.lt_succ_self _)

/-- The single field assembled from the installed stages has the product
offspring law. Every finite set of coordinates agrees with one stage. -/
theorem RootIndexed.restartedRealPositionTrajectoryField_measurable_law
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (selectedBRWPopulation : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α ℝ) Root α ℝ
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := ℝ))
      RootIndexed.StepField.left)
    (hselectedBRWPopulationFiniteSlices : selectedBRWPopulation.FiniteSlices) :
    let V := RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id
      hselectedBRWPopulationFiniteSlices.toFinset
    Measurable V ∧ (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map V =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  dsimp only
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Root) μ
  let population := hselectedBRWPopulationFiniteSlices.toFinset
  let V := RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id population
  let S := RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id population
  have hS (n : ℕ) : Measurable (S n) ∧ P.map (S n) = Q := by
    simpa only [S, P, Q, population, RootIndexed.restartedRealPositionNSelectedBRWField,
      show RootIndexed.StepField.left = (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ) from rfl] using
      RootIndexed.rankInstalledField_causalPopulation_measurable_law μ N roots initialPosition
        id measurable_id id measurable_id selectedBRWPopulation hselectedBRWPopulationFiniteSlices n
  have hV : Measurable V := by
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact ((measurable_pi_apply u).comp (measurable_pi_apply r)).comp (hS (u.length + 1)).1
  refine ⟨hV, ?_⟩
  change P.map V = Q
  let uncurry := (MeasurableEquiv.curry Root (TreeNode α) (Step α ℝ)).symm
  have hQ : Q.map uncurry = Measure.infinitePi (fun _ : Root × TreeNode α => μ) := by
    simpa only [Q, RootIndexed.stepFieldLaw, ProbabilityTheory.BranchingProcess.offspringFieldLaw,
      uncurry] using (Measure.infinitePi_map_curry_symm
        (μ := fun (_ : Root) (_ : TreeNode α) => μ))
  apply uncurry.map_measurableEquiv_injective
  rw [hQ]
  apply Measure.eq_infinitePi
  intro s t ht
  let n := s.sup (fun p => p.2.length + 1)
  have hbox := MeasurableSet.pi s.countable_toSet (fun p _ => ht p)
  rw [Measure.map_map uncurry.measurable hV, Measure.map_apply (uncurry.measurable.comp hV) hbox]
  have hevent : (uncurry ∘ V) ⁻¹' Set.pi (↑s) t =
      (uncurry ∘ S n) ⁻¹' Set.pi (↑s) t := by
    ext field
    change (∀ p ∈ s, V field p.1 p.2 ∈ t p) ↔ ∀ p ∈ s, S n field p.1 p.2 ∈ t p
    have hcoord (p : Root × TreeNode α) (hp : p ∈ s) : V field p.1 p.2 = S n field p.1 p.2 :=
      RootIndexed.restartedRealPositionTrajectoryField_eq_stage N roots initialPosition id population field n p.1 p.2
        (Nat.lt_of_succ_le (Finset.le_sup (f := fun q : Root × TreeNode α => q.2.length + 1) hp))
    exact ⟨fun h p hp => hcoord p hp ▸ h p hp, fun h p hp => (hcoord p hp).symm ▸ h p hp⟩
  rw [hevent, ← Measure.map_apply (uncurry.measurable.comp (hS n).1) hbox,
    ← Measure.map_map uncurry.measurable (hS n).1, (hS n).2, hQ]
  exact Measure.infinitePi_pi (fun _ => μ) (fun p _ => ht p)


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
