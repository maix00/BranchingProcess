/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Capacity
import Probability.BranchingRandomWalk.Population.Processes.Selected.Continuation
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
import Mathlib.Order.Sum.Order

/-!
# Endpoint upper-tail order for first-N selection

## Public declarations

* `RootIndexed.selectedPopulationEndpointAtLeast` is the event that
  every selected position at generation $H$ is at least $x$.
* `RootIndexed.measurableSet_selectedPopulationEndpointAtLeast`: the event
  ${X_H(p)\ge x\text{ for all }p\in P_H\}$ is measurable.
* `RootIndexed.selectedPopulationEndpointAtLeast_add_initial`: translating
  the initial positions and threshold by $c$ leaves the upper-tail event equal.
* `RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_initialEmbedding`:
  for two finite initial clouds, if the smaller cloud can be matched
  injectively to particles at weakly smaller positions in the larger cloud,
  then the larger cloud has the smaller probability of having every
  generation-$H$ particle at or above $x$.
* `RootIndexed.measure_selectedPopulationEndpointAtLeast_relabel`: an injective
  relabeling preserving the tie order gives the same endpoint probability.
* `RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_cloudEmbedding`:
  the same upper-tail comparison holds for initial clouds on distinct
  finite label types, each with its own order for ties.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching Combinatorics.UlamHarris

/-- The upper-tail event for the minimum, with the empty cloud assigned
minimum $+\infty$. -/
def RootIndexed.selectedPopulationEndpointAtLeast
    {Root α : Type*} [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ) (H : ℕ) (x : ℝ) :
    Set (RootIndexed.StepField Root α ℝ) :=
  {field | ∀ p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id H field,
    x ≤ RootIndexed.position initialPosition id field p.1 p.2}

theorem RootIndexed.measurableSet_selectedPopulationEndpointAtLeast
    {Root α : Type*} [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ) (H : ℕ) (x : ℝ) :
    MeasurableSet (RootIndexed.selectedPopulationEndpointAtLeast (α := α)
      N roots initialPosition H x) := by
  rw [show RootIndexed.selectedPopulationEndpointAtLeast (α := α) N roots initialPosition H x =
      ⋂ p : RootIndexed.TreeNode Root α, {field |
        p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id H field →
        x ≤ RootIndexed.position initialPosition id field p.1 p.2} by
    ext field
    simp only [RootIndexed.selectedPopulationEndpointAtLeast, Set.mem_iInter, Set.mem_ofPred_eq]]
  apply MeasurableSet.iInter
  intro p
  have hpopulation := (RootIndexed.selectedPopulationTotalized_adapted (α := α)
    N roots initialPosition id measurable_id id measurable_id H).mono
      ((RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)).le H) le_rfl
  have hposition := (RootIndexed.position_measurable (α := α) initialPosition id
    measurable_id p.1 p.2).mono
      ((RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)).le p.2.length) le_rfl
  exact (hpopulation (measurableSet_mem_finset p)).imp (hposition measurableSet_Ici)

/-- Translate both the initial cloud and its endpoint threshold. -/
theorem RootIndexed.selectedPopulationEndpointAtLeast_add_initial
    {Root α : Type*} [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initial : Root → ℝ) (H : ℕ) (x c : ℝ) :
    RootIndexed.selectedPopulationEndpointAtLeast (α := α) N roots (fun r => initial r + c) H (x + c) =
      RootIndexed.selectedPopulationEndpointAtLeast N roots initial H x := by
  ext field
  change (∀ p ∈ RootIndexed.selectedPopulationTotalized N roots (fun r => initial r + c)
      id id H field, x + c ≤ RootIndexed.position (fun r => initial r + c) id field p.1 p.2) ↔ _
  rw [RootIndexed.selectedPopulationTotalized_add_initial N roots initial id field c H]
  simp [RootIndexed.selectedPopulationEndpointAtLeast, RootIndexed.position,
    add_right_comm (initial _) c]

open ProbabilityTheory.BranchingRandomWalk.Coupling in
/-- Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (Fudan University, 2026), Chapter 3, Corollary 3.10,
applied to upper-tail endpoint events. -/
theorem RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_initialEmbedding
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)] [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (N : ℕ) (hN : 0 < N) (roots₁ roots₂ : Finset Root) (hsize : roots₁.card ≤ N)
    (initial : Root → ℝ) (matchRoot : Root → Root)
    (hmap : Set.MapsTo matchRoot (↑roots₁ : Set Root) ↑roots₂)
    (hinj : Set.InjOn matchRoot (↑roots₁ : Set Root))
    (hpos : ∀ r ∈ roots₁, initial (matchRoot r) ≤ initial r)
    (H : ℕ) (x : ℝ) :
    RootIndexed.stepFieldLaw (Root := Root) μ
      (RootIndexed.selectedPopulationEndpointAtLeast N roots₂ initial H x) ≤
    RootIndexed.stepFieldLaw (Root := Root) μ
      (RootIndexed.selectedPopulationEndpointAtLeast N roots₁ initial H x) := by
  obtain ⟨hm, hright, hleft, hcompare⟩ :=
    RootIndexed.selectedPopulationCoupling_of_capacity_le_ae μ hleftFinite
      N N hN le_rfl roots₁ roots₂ hsize initial matchRoot hmap hinj hpos
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let L : RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ :=
    RootIndexed.StepField.left
  let R := RootIndexed.restartedRealPositionTrajectoryField N roots₂ initial id
    (fun n field => RootIndexed.selectedPopulationTotalized N roots₁ initial id id n (L field))
  let A := RootIndexed.selectedPopulationEndpointAtLeast (α := α) N roots₂ initial H x
  let B := RootIndexed.selectedPopulationEndpointAtLeast (α := α) N roots₁ initial H x
  have hR : Measurable R := hm
  have hL : Measurable L := by
    rw [measurable_pi_iff]
    intro r
    exact measurable_pi_apply (Sum.inl r)
  change P.map R = _ at hright
  change P.map L = _ at hleft
  have hRA : P (R ⁻¹' A) = RootIndexed.stepFieldLaw μ A := by
    rw [← Measure.map_apply hR
      (RootIndexed.measurableSet_selectedPopulationEndpointAtLeast N roots₂ initial H x), hright]
  have hLB : P (L ⁻¹' B) = RootIndexed.stepFieldLaw μ B := by
    rw [← Measure.map_apply hL
      (RootIndexed.measurableSet_selectedPopulationEndpointAtLeast N roots₁ initial H x), hleft]
  change RootIndexed.stepFieldLaw μ A ≤ RootIndexed.stepFieldLaw μ B
  rw [← hRA, ← hLB]
  apply measure_mono_ae
  filter_upwards [hcompare] with field hfield hA
  have hminimum := (hfield H).2
  change (RootIndexed.selectedPopulationTotalized N roots₂ initial id id H (R field)).inf
      (fun q => ((RootIndexed.position initial id (R field) q.1 q.2 : ℝ) : WithTop ℝ)) ≤
    (RootIndexed.selectedPopulationTotalized N roots₁ initial id id H (L field)).inf
      (fun p => ((RootIndexed.position initial id (L field) p.1 p.2 : ℝ) : WithTop ℝ)) at hminimum
  have hb : (x : WithTop ℝ) ≤
      (RootIndexed.selectedPopulationTotalized N roots₂ initial id id H (R field)).inf
        (fun q => ((RootIndexed.position initial id (R field) q.1 q.2 : ℝ) : WithTop ℝ)) :=
    Finset.le_inf fun p hp => WithTop.coe_le_coe.mpr (hA p hp)
  intro p hp
  exact WithTop.coe_le_coe.mp ((hb.trans hminimum).trans (Finset.inf_le hp))

/-- Transport the endpoint event along an injective relabeling that
preserves the order on the embedded genealogical labels. -/
theorem RootIndexed.measure_selectedPopulationEndpointAtLeast_relabel
    {Root κ α : Type*} [Fintype κ] [DecidableEq Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)] [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace (RootIndexed.TreeNode κ α)] [Countable (RootIndexed.TreeNode κ α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode κ α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (f : κ → Root) (hf : Function.Injective f)
    (horder : ∀ p q : RootIndexed.TreeNode κ α, p < q ↔ (f p.1, p.2) < (f q.1, q.2))
    (N : ℕ) (initial : Root → ℝ) (H : ℕ) (x : ℝ) :
    RootIndexed.stepFieldLaw (Root := Root) μ
      (RootIndexed.selectedPopulationEndpointAtLeast N (Finset.univ.image f) initial H x) =
    RootIndexed.stepFieldLaw (Root := κ) μ
      (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (initial ∘ f) H x) := by
  let roots (i : κ) : RootIndexed.TreeNode Root α := (f i, [])
  let subtrees := RootIndexed.subtreeStepFieldVector (X := ℝ) roots
  have hinj : Function.Injective roots := fun _ _ h => hf (congrArg Prod.fst h)
  have hlaw := RootIndexed.subtreeStepFieldVector_law μ roots (fun _ => rfl) hinj
  have hmeas := RootIndexed.subtreeStepFieldVector_measurable (X := ℝ) roots
  rw [← hlaw, Measure.map_apply hmeas
    (RootIndexed.measurableSet_selectedPopulationEndpointAtLeast N Finset.univ (initial ∘ f) H x)]
  congr 1
  ext field
  have hcover : Finset.univ.image roots = RootIndexed.selectedPopulationTotalized
      N (Finset.univ.image f) initial id id 0 field := by
    ext p
    simp [RootIndexed.selectedPopulationTotalized, RootIndexed.mem_initialPopulation_iff,
      Finset.mem_image, roots, eq_comm]
  have hinit : RootIndexed.subtreeInitialPosition initial id field roots = initial ∘ f := by
    funext i
    simp [RootIndexed.subtreeInitialPosition, roots, RootIndexed.position,
      RootIndexed.displace]
  have hpop := RootIndexed.selectedPopulationTotalized_eq_image_subtrees
    N (Finset.univ.image f) initial id id field 0 roots (fun _ => rfl) hinj hcover
    (by simpa [roots] using horder) H
  rw [hinit] at hpop
  simp only [Nat.zero_add, roots, List.nil_append] at hpop
  change (∀ p ∈ RootIndexed.selectedPopulationTotalized
    N (Finset.univ.image f) initial id id H field,
      x ≤ RootIndexed.position initial id field p.1 p.2) ↔
    ∀ p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ (initial ∘ f) id id H (subtrees field),
      x ≤ RootIndexed.position (initial ∘ f) id (subtrees field) p.1 p.2
  rw [hpop]
  have hpos (p : RootIndexed.TreeNode κ α) :
      RootIndexed.position (initial ∘ f) id (subtrees field) p.1 p.2 =
      RootIndexed.position initial id field (f p.1) p.2 := by
    rw [← hinit]
    exact RootIndexed.position_subtreeStepFieldVector initial id field roots p.1 p.2
  constructor
  · intro h p hp
    rw [hpos]
    exact h _ (Finset.mem_image_of_mem _ hp)
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (hpos q) ▸ h q hq

/-- The comparison by injection of initial positions is invariant under
independent choices of genealogical labels on the two initial clouds. -/
theorem RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_cloudEmbedding
    {κ₁ κ₂ α : Type*} [Fintype κ₁] [Fintype κ₂] [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode κ₁ α)] [Countable (RootIndexed.TreeNode κ₁ α)]
    [MeasurableSpace (RootIndexed.TreeNode κ₂ α)] [Countable (RootIndexed.TreeNode κ₂ α)]
    [LinearOrder (RootIndexed.TreeNode κ₁ α)] [LinearOrder (RootIndexed.TreeNode κ₂ α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hleftFinite : ∀ᵐ ξ ∂μ, ξ.IsLeftLocallyFinite)
    (N : ℕ) (hN : 0 < N) (hsize : Fintype.card κ₁ ≤ N)
    (x₁ : κ₁ → ℝ) (x₂ : κ₂ → ℝ) (matchRoot : κ₁ ↪ κ₂)
    (hpos : ∀ i, x₂ (matchRoot i) ≤ x₁ i) (H : ℕ) (x : ℝ) :
    RootIndexed.stepFieldLaw (Root := κ₂) μ
      (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ x₂ H x) ≤
    RootIndexed.stepFieldLaw (Root := κ₁) μ
      (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ x₁ H x) := by
  classical
  let tag (p : RootIndexed.TreeNode (κ₁ ⊕ κ₂) α) :
      (RootIndexed.TreeNode κ₁ α) ⊕ₗ (RootIndexed.TreeNode κ₂ α) :=
    match p.1 with
    | .inl i => toLex (Sum.inl (i, p.2))
    | .inr i => toLex (Sum.inr (i, p.2))
  have htag : Function.Injective tag := by
    rintro ⟨i, v⟩ ⟨j, w⟩ h
    cases i <;> cases j <;> simp_all [tag, toLex.injective.eq_iff, Prod.mk.injEq]
  let _ : LinearOrder (RootIndexed.TreeNode (κ₁ ⊕ κ₂) α) := LinearOrder.lift' tag htag
  let _ : MeasurableSpace (RootIndexed.TreeNode (κ₁ ⊕ κ₂) α) := ⊤
  let initial := Sum.elim x₁ x₂
  have hl (p q : RootIndexed.TreeNode κ₁ α) :
      p < q ↔ ((Sum.inl p.1 : κ₁ ⊕ κ₂), p.2) < (Sum.inl q.1, q.2) := by
    change p < q ↔ toLex (Sum.inl p : RootIndexed.TreeNode κ₁ α ⊕ RootIndexed.TreeNode κ₂ α) <
      toLex (Sum.inl q)
    exact Sum.Lex.inl_lt_inl_iff.symm
  have hr (p q : RootIndexed.TreeNode κ₂ α) :
      p < q ↔ ((Sum.inr p.1 : κ₁ ⊕ κ₂), p.2) < (Sum.inr q.1, q.2) := by
    change p < q ↔ toLex (Sum.inr p : RootIndexed.TreeNode κ₁ α ⊕ RootIndexed.TreeNode κ₂ α) <
      toLex (Sum.inr q)
    exact Sum.Lex.inr_lt_inr_iff.symm
  rw [← show _ = RootIndexed.stepFieldLaw μ
        (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ x₁ H x) from
      RootIndexed.measure_selectedPopulationEndpointAtLeast_relabel μ Sum.inl Sum.inl_injective hl N initial H x,
    ← show _ = RootIndexed.stepFieldLaw μ
        (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ x₂ H x) from
      RootIndexed.measure_selectedPopulationEndpointAtLeast_relabel μ Sum.inr Sum.inr_injective hr N initial H x]
  let assign : κ₁ ⊕ κ₂ → κ₁ ⊕ κ₂ := Sum.elim (Sum.inr ∘ matchRoot) Sum.inr
  refine RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_initialEmbedding
    μ hleftFinite N hN _ _ ?_ initial assign ?_ ?_ ?_ H x
  · simpa [Finset.card_image_of_injective _ Sum.inl_injective] using hsize
  · rintro _ hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨matchRoot i, Finset.mem_univ _, rfl⟩
  · rintro _ hp _ hq heq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg Sum.inl (matchRoot.injective (Sum.inr_injective heq))
  · rintro _ hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hpos i

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
