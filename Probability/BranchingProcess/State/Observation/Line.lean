/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Observation.Basic
public import Probability.Process.Tree.Line.Information.Boundary
public import Mathlib.Data.List.Basic

/-!
# Inherited states at a cut of the canonical generation process

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`, put
`initial = σ(rootStates)` and `coordinate u = σ(offspringStates u)`.

* `stateAt_measurable_ancestralPast` proves that `X_u` is measurable in the
  initial information and strict ancestors' reproduction observations.
* `descendantTree_measurable_linePast` proves that a complete subtree
  incomparable with a cut is observable in that cut's past.
* `linePast_generation_eq_piLE` identifies the line information at generation `n`
  with the native canonical filtration `Filtration.piLE n`.
* `stateAt_measurable_selected` proves that an `F_L`-observable choice `R ∈ L`
  with countable range has inherited state `X_R` measurable in `F_L`, for an
  arbitrary optional line `L` of this generation process.

These are actual observations of the existing state process. There is no
probability-law premise or new tree construction. Boundary-state observability
is derived from the parent's recorded offspring family, including the root
case from the initial observation. The optional-line step invokes the general
`ProbabilityTheory.Tree.IsOptionalLine.measurable_selected_state`.

The information convention is that of P. Jagers and A. N. Lagerås,
*General branching processes conditioned on extinction are still branching
processes* (2008), §2.2–2.3, pp. 542–543, DOI 10.1214/ECP.v13-1419.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open MeasureTheory Combinatorics.UlamHarris Finset Preorder

variable {Root α S : Type*} [MeasurableSpace S]

local notation "initialInformation" => MeasurableSpace.comap
  (rootStates (Root := Root) (α := α) (S := S)) inferInstance
local notation "reproductionInformation" =>
  fun u : RootIndexed.TreeNode Root α =>
    MeasurableSpace.comap (offspringStates (S := S) u) inferInstance

/-- A node's inherited state is observed at birth, before it reproduces. -/
theorem stateAt_measurable_ancestralPast (u : RootIndexed.TreeNode Root α) :
    Measurable[Tree.ancestralPast initialInformation reproductionInformation u]
      (stateAt (S := S) u) := by
  rcases u with ⟨r, v⟩
  by_cases hv : v = []
  · subst v
    change Measurable[Tree.ancestralPast initialInformation reproductionInformation (r, [])]
      (fun x => rootStates x r)
    have hm : Measurable[
        Tree.ancestralPast initialInformation reproductionInformation (r, [])]
        (rootStates (Root := Root) (α := α) (S := S)) :=
      Measurable.of_comap_le le_sup_left
    exact (measurable_pi_apply r).comp hm
  · have hparent : RootIndexed.IsAncestor (r, v.dropLast) (r, v) :=
      ⟨rfl, v.dropLast_prefix⟩
    have hne : (r, v.dropLast) ≠ (r, v) := by
      intro heq
      have hlen := congrArg (fun p : RootIndexed.TreeNode Root α => p.2.length) heq
      simp only [List.length_dropLast] at hlen
      have hpos : 0 < v.length := List.length_pos_iff.mpr hv
      omega
    have hp := Tree.coordinate_le_ancestralPast initialInformation reproductionInformation
      hparent hne
    have hm : Measurable[Tree.ancestralPast initialInformation reproductionInformation (r, v)]
        (fun x => offspringStates (r, v.dropLast) x (v.getLast hv)) :=
      (measurable_pi_apply (v.getLast hv)).comp (Measurable.of_comap_le hp)
    simpa only [offspringStates, List.dropLast_append_getLast] using hm

/-- The whole subtree on a branch disjoint from a cut is already in that cut's past. -/
theorem descendantTree_measurable_linePast
    (u : RootIndexed.TreeNode Root α) (ℓ : Set (RootIndexed.TreeNode Root α))
    (hline : RootIndexed.IsLine (insert u ℓ)) (hu : u ∉ ℓ) :
    Measurable[Tree.linePast initialInformation reproductionInformation ℓ]
      (descendantTree (S := S) u) := by
  let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
    Tree.linePast initialInformation reproductionInformation ℓ
  rw [measurable_pi_iff]
  intro v
  have hinfo : Tree.ancestralPast initialInformation reproductionInformation
      (u.1, u.2 ++ v) ≤ Tree.linePast initialInformation reproductionInformation ℓ := by
    apply Tree.ancestralPast_le_linePast_of_no_strict_ancestor
    intro w hw hwv
    have heq : w = u := hline.eq_of_common_descendant
      (Set.mem_insert_of_mem _ hw) (Set.mem_insert _ _) hwv ⟨rfl, List.prefix_append _ _⟩
    exact False.elim (hu (heq ▸ hw))
  exact (stateAt_measurable_ancestralPast (S := S) (u.1, u.2 ++ v)).mono hinfo le_rfl

/-- The reproduction-based line information recovers the canonical generation filtration. -/
theorem linePast_generation_eq_piLE (n : ℕ) :
    Tree.linePast initialInformation reproductionInformation
      {u : RootIndexed.TreeNode Root α | u.2.length = n} =
    Filtration.piLE (X := fun k : ℕ => (Root × (Fin k → α)) → Option S) n := by
  have hread (k : ℕ) (hk : k ≤ n) :
      Measurable[Filtration.piLE (X := fun k : ℕ => (Root × (Fin k → α)) → Option S) n]
        (fun x : Π k : ℕ, (Root × (Fin k → α)) → Option S => x k) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    have hf : Measurable[MeasurableSpace.comap (frestrictLe n) inferInstance]
        (frestrictLe n : (Π k : ℕ, (Root × (Fin k → α)) → Option S) → _) :=
      Measurable.of_comap_le le_rfl
    exact (measurable_pi_apply (⟨k, Finset.mem_Iic.mpr hk⟩ : Finset.Iic n)).comp hf
  apply le_antisymm
  · let : MeasurableSpace (Π k : ℕ, (Root × (Fin k → α)) → Option S) :=
      Filtration.piLE (X := fun k : ℕ => (Root × (Fin k → α)) → Option S) n
    rw [Tree.linePast_generation]
    refine sup_le ?_ (iSup_le fun u => iSup_le fun hu => ?_)
    · rw [← measurable_iff_comap_le]
      rw [measurable_pi_iff]
      intro r
      exact (measurable_pi_apply (r, [].get)).comp (hread 0 (Nat.zero_le n))
    · rw [← measurable_iff_comap_le]
      rw [measurable_pi_iff]
      intro j
      have hlen : (u.2 ++ [j]).length ≤ n := by
        simp only [List.length_append, List.length_singleton]
        omega
      exact (measurable_pi_apply (u.1, (u.2 ++ [j]).get)).comp (hread _ hlen)
  · let : MeasurableSpace (Π k : ℕ, (Root × (Fin k → α)) → Option S) :=
      Tree.linePast initialInformation reproductionInformation
        {u : RootIndexed.TreeNode Root α | u.2.length = n}
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rw [← measurable_iff_comap_le]
    rw [measurable_pi_iff]
    intro k
    rw [measurable_pi_iff]
    intro p
    let u : RootIndexed.TreeNode Root α := (p.1, List.ofFn p.2)
    have hlen : u.2.length ≤ n := by simpa only [u, List.length_ofFn] using
      (Finset.mem_Iic.mp k.2)
    have hinfo : Tree.ancestralPast initialInformation reproductionInformation u ≤
        Tree.linePast initialInformation reproductionInformation
          {v : RootIndexed.TreeNode Root α | v.2.length = n} := by
      apply Tree.ancestralPast_le_linePast_of_no_strict_ancestor
      intro v hv hvu
      have hlength : v.2.length = u.2.length := by
        have hle := hvu.2.length_le
        change v.2.length = n at hv
        omega
      exact Prod.ext hvu.1 (hvu.2.eq_of_length hlength)
    have hm := (stateAt_measurable_ancestralPast (S := S) u).mono hinfo le_rfl
    have heq : stateAt (S := S) u =
        (fun x : Π k : ℕ, (Root × (Fin k → α)) → Option S => x k.1 p) := by
      funext x
      exact stateAt_ofFn x k.1 p
    rwa [heq] at hm

/-- The generic optional-line boundary theorem applies to the actual inherited
states of the canonical generation process, on arbitrary measurable state spaces. -/
theorem stateAt_measurable_selected
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (choice : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      RootIndexed.TreeNode Root α)
    (hcount : (Set.range choice).Countable)
    (hchoice : ∀ u, MeasurableSet[h.measurableSpace] {x | choice x = u})
    (hmem : ∀ x, choice x ∈ L x) :
    Measurable[h.measurableSpace] (fun x => stateAt (choice x) x) :=
  h.measurable_selected_state initialInformation reproductionInformation
    rootStates_measurable.comap_le (fun u => (offspringStates_measurable u).comap_le)
    stateAt stateAt_measurable_ancestralPast choice hcount hchoice hmem


end ProbabilityTheory.BranchingProcess.State

end
