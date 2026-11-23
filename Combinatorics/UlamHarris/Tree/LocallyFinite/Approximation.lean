/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.LocallyFinite.Space
public import Combinatorics.UlamHarris.Tree.Finite.Basic
public import Combinatorics.UlamHarris.Tree.Topology.Metric.Completeness
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Finite approximations of locally finite trees

## Public declarations

In namespace `Combinatorics.UlamHarris.Tree`:

* `IsLocallyFinite.isFinite_truncate` proves that every finite-depth
  truncation of a locally finite tree has finitely many nodes.
* `isLocallyFinite_iff_finite_truncations` and
  `isLocallyFinite_iff_finite_levels` identify nodewise, finite-truncation,
  and finite-generation definitions of local finiteness.
* `isClosed_isLocallyFinite` proves local finiteness is closed in depth distance.
* `LocallyFinite.completeSpace_metricSpace` proves completeness of the
  restricted depth metric.
* `LocallyFinite.finiteTrees_denseRange` states that finite trees are dense
  in the locally finite tree space for the depth metric.

The approximation is by truncating generations in the rooted-tree setting of
J. Neveu, "Arbres et processus de Galton--Watson", Section 2,
*Annales de l'I.H.P. Probabilités et statistiques* 22(2) (1986), 199--207,
https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
open scoped Topology
namespace Combinatorics.UlamHarris.Tree
variable {α : Type*} [LT α]

/-- Finitely many generations of a locally finite rooted tree have finitely many nodes. -/
theorem IsLocallyFinite.isFinite_truncate {T : Tree α} (hT : T.IsLocallyFinite)
    (n : ℕ) : (T.truncate n).IsFinite := by
  induction n with
  | zero =>
    apply (Set.finite_singleton ([] : List α)).subset
    intro u hu
    have hz : u.length = 0 := Nat.eq_zero_of_le_zero hu.1
    simpa using List.length_eq_zero_iff.mp hz
  | succ n ih =>
    have hchildren : (⋃ u ∈ (T.truncate n).carrier,
        (fun j : α ↦ u ++ [j]) '' {j | u ++ [j] ∈ T.carrier}).Finite :=
      ih.biUnion (fun u _ ↦ (hT u).image _)
    apply (ih.union hchildren).subset
    intro u hu
    by_cases hlen : u.length ≤ n
    · exact Or.inl ⟨hlen, hu.2⟩
    · apply Or.inr
      induction u using List.reverseRecOn with
      | nil => simp at hlen
      | append_singleton v j _ =>
        simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
        refine ⟨v, ⟨?_, T.parent_closed hu.2⟩, j, hu.2, rfl⟩
        have hv : (v ++ [j]).length ≤ n + 1 := hu.1
        simp only [List.length_append, List.length_singleton] at hv
        omega

/-- Nodewise local finiteness is equivalent to finiteness of every generation truncation. -/
theorem isLocallyFinite_iff_finite_truncations (T : Tree α) :
    T.IsLocallyFinite ↔ ∀ n, (T.truncate n).IsFinite := by
  constructor
  · exact fun h n ↦ h.isFinite_truncate n
  · intro h u
    have hf := (h (u.length + 1)).preimage (f := fun i : α ↦ u ++ [i])
      (fun a _ b _ hab ↦ by simpa using List.append_right_injective u hab)
    change {i : α | (u ++ [i]).length ≤ u.length + 1 ∧ u ++ [i] ∈ T.carrier}.Finite at hf
    simpa only [List.length_append, List.length_singleton, le_refl, true_and] using hf

/-- Equivalently, every generation of the rooted tree is finite. -/
theorem isLocallyFinite_iff_finite_levels (T : Tree α) :
    T.IsLocallyFinite ↔ ∀ n, {u ∈ T.carrier | u.length = n}.Finite := by
  constructor
  · intro h n
    exact (h.isFinite_truncate n).subset (fun _ hu ↦ ⟨hu.2.le, hu.1⟩)
  · intro h
    rw [isLocallyFinite_iff_finite_truncations]
    intro n
    have hf := (Set.finite_Iic n).biUnion (fun k _ ↦ h k)
    apply hf.subset
    intro u hu
    simp only [Set.mem_iUnion]
    exact ⟨u.length, hu.1, hu.2, rfl⟩

/-- Local finiteness is closed under depth-metric limits. -/
theorem isClosed_isLocallyFinite :
    @IsClosed (Tree α) (treeMetricTopology α) {T | T.IsLocallyFinite} := by
  let : MetricSpace (Tree α) := treeMetricSpace α
  let : TopologicalSpace (Tree α) := treeMetricTopology α
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro T hT
  have hnot : ¬ ∀ u : List α, {i | u ++ [i] ∈ T.carrier}.Finite := hT
  obtain ⟨u, hu⟩ := not_forall.mp hnot
  refine ⟨(1 + (u.length : ℝ))⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro S hS hfin
  have he : S.truncate (u.length + 1) = T.truncate (u.length + 1) :=
    (mem_truncationBall_iff_treeDist_lt T S u.length).mpr hS
  have hc : {i | u ++ [i] ∈ S.carrier} = {i | u ++ [i] ∈ T.carrier} := by
    ext i
    change (u ++ [i] ∈ S.carrier) ↔ (u ++ [i] ∈ T.carrier)
    have hm := congrArg (fun R : Tree α ↦ u ++ [i] ∈ R.carrier) he
    simpa only [mem_truncate, List.length_append, List.length_singleton,
      le_refl, true_and] using Iff.of_eq hm
  exact hu (hc ▸ hfin u)

namespace LocallyFinite

/-- A closed subspace of the complete tree space is complete. -/
theorem completeSpace_metricSpace (α : Type*) [LT α] :
    @CompleteSpace (LocallyFiniteTree α) (metricSpace α).toUniformSpace := by
  let : MetricSpace (Tree α) := treeMetricSpace α
  let : CompleteSpace (Tree α) := completeSpace_treeMetricSpace α
  exact isClosed_isLocallyFinite.isComplete.completeSpace_coe

/-- Finite trees approximate every locally finite tree by generation truncation. -/
theorem finiteTrees_denseRange :
    @DenseRange (LocallyFiniteTree α) (metricTopology α) (FiniteTree α)
      (toLocallyFinite α) := by
  let : MetricSpace (Tree α) := treeMetricSpace α
  let : MetricSpace (LocallyFiniteTree α) := metricSpace α
  rw [Metric.denseRange_iff]
  intro T ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨⟨T.1.truncate (n + 1), T.2.isFinite_truncate _⟩, ?_⟩
  have hd : treeDist (T.1.truncate (n + 1)) T.1 < (1 + (n : ℝ))⁻¹ := by
    rw [← mem_truncationBall_iff_treeDist_lt]
    simp [mem_truncationBall]
  have hr : (1 + (n : ℝ))⁻¹ < ε := by simpa [one_div, add_comm] using hn
  change treeDist T.1 (T.1.truncate (n + 1)) < ε
  rw [treeDist_comm]
  exact hd.trans hr

end LocallyFinite
end Combinatorics.UlamHarris.Tree
