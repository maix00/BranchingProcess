/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Observation.Line

/-!
# Complete information outside a descendant tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `complementObservation a u` records the generation history through `a` and
  the complete descendant trees at all depth-`a` nodes other than `u`.
* `linePast_singleton_eq_comap_complementObservation` identifies its information
  exactly with `linePast σ(rootStates) σ(offspringStates) {u}`. Thus the
  one-node ordinary branching identity can be read with the same line information
  used by optional cuts.

The maps read the existing generation path. No probability, independence,
standard-Borel or countability hypothesis enters this information equality.
The outside-descendant convention is P. Jagers and A. N. Lagerås,
*General branching processes conditioned on extinction are still branching
processes* (2008), §2.2–2.3, pp. 542–543, DOI 10.1214/ECP.v13-1419.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open MeasureTheory Combinatorics.UlamHarris Finset Preorder

variable {Root α S : Type*}

/-- History through the node's generation and the complete other trees of that generation. -/
def complementObservation (a : ℕ) (u : Root × (Fin a → α))
    (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
  (frestrictLe a x, fun q : {q : Root × (Fin a → α) // q ≠ u} =>
    descendantTree (q.1.1, List.ofFn q.1.2) x)

variable [MeasurableSpace S]

local notation "initialInformation" => MeasurableSpace.comap
  (rootStates (Root := Root) (α := α) (S := S)) inferInstance
local notation "reproductionInformation" =>
  fun u : RootIndexed.TreeNode Root α =>
    MeasurableSpace.comap (offspringStates (S := S) u) inferInstance

private lemma stateAt_measurable_singleton (u w : RootIndexed.TreeNode Root α)
    (hno : RootIndexed.IsAncestor u w → u = w) :
    Measurable[Tree.linePast initialInformation reproductionInformation {u}]
      (stateAt (S := S) w) := by
  apply (stateAt_measurable_ancestralPast w).mono _ le_rfl
  apply Tree.ancestralPast_le_linePast_of_no_strict_ancestor
  intro v hv hvw
  have heq : v = u := Set.mem_singleton_iff.mp hv
  subst v
  exact hno hvw

private lemma stateAt_measurable_complement (a : ℕ) (u : Root × (Fin a → α))
    (w : RootIndexed.TreeNode Root α)
    (hno : RootIndexed.IsAncestor (u.1, List.ofFn u.2) w → (u.1, List.ofFn u.2) = w) :
    Measurable[MeasurableSpace.comap (complementObservation (S := S) a u) inferInstance]
      (stateAt (S := S) w) := by
  let info := MeasurableSpace.comap (complementObservation (S := S) a u) inferInstance
  let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) := info
  have hobs : Measurable (complementObservation (S := S) a u) :=
    Measurable.of_comap_le le_rfl
  have hH : Measurable (frestrictLe a : (Π n : ℕ, (Root × (Fin n → α)) → Option S) → _) :=
    measurable_fst.comp hobs
  by_cases hw : w.2.length ≤ a
  · exact (measurable_pi_apply (w.1, w.2.get)).comp
      ((measurable_pi_apply (⟨w.2.length, Finset.mem_Iic.mpr hw⟩ : Iic a)).comp hH)
  · have ha : a ≤ w.2.length := by omega
    have hlen : (w.2.take a).length = a := by simp [Nat.min_eq_left ha]
    let f : Fin a → α := fun j => (w.2.take a).get (Fin.cast hlen.symm j)
    have hf : List.ofFn f = w.2.take a := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, hlen]
      · intro j hj hj'
        simp [f]
    let q : Root × (Fin a → α) := (w.1, f)
    have hprefix : RootIndexed.IsAncestor (q.1, List.ofFn q.2) w := by
      exact ⟨rfl, hf ▸ List.take_prefix a w.2⟩
    have hqu : q ≠ u := by
      intro heq
      have hanc : RootIndexed.IsAncestor (u.1, List.ofFn u.2) w := heq ▸ hprefix
      have he := congrArg (fun v : RootIndexed.TreeNode Root α => v.2.length) (hno hanc)
      simp only [List.length_ofFn] at he
      omega
    have hm : Measurable (fun x =>
        descendantTree (q.1, List.ofFn q.2) x (w.2.drop a)) :=
      (measurable_pi_apply (w.2.drop a)).comp
        ((measurable_pi_apply (⟨q, hqu⟩ : {q : Root × (Fin a → α) // q ≠ u})).comp
          (measurable_snd.comp hobs))
    have heq : (fun x => descendantTree (q.1, List.ofFn q.2) x (w.2.drop a)) =
        stateAt (S := S) w := by
      funext x
      simp only [descendantTree, q, hf, List.take_append_drop]
    rwa [heq] at hm

/-- The complete complement observation is exactly the singleton line past. -/
theorem linePast_singleton_eq_comap_complementObservation (a : ℕ)
    (u : Root × (Fin a → α)) :
    Tree.linePast initialInformation reproductionInformation {(u.1, List.ofFn u.2)} =
      MeasurableSpace.comap (complementObservation (S := S) a u) inferInstance := by
  apply le_antisymm
  · refine sup_le ?_ (iSup_le fun v => iSup_le fun hv => ?_)
    · rw [← measurable_iff_comap_le]
      let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
        MeasurableSpace.comap (complementObservation (S := S) a u) inferInstance
      rw [measurable_pi_iff]
      intro r
      exact stateAt_measurable_complement a u (r, []) (fun hanc => by
        apply Prod.ext hanc.1
        exact hanc.2.eq_of_length_le (by simp))
    · rw [← measurable_iff_comap_le]
      let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
        MeasurableSpace.comap (complementObservation (S := S) a u) inferInstance
      rw [measurable_pi_iff]
      intro j
      apply stateAt_measurable_complement a u (v.1, v.2 ++ [j])
      intro hanc
      by_contra hne
      have hlt : (List.ofFn u.2).length < (v.2 ++ [j]).length := by
        have hle := hanc.2.length_le
        change (List.ofFn u.2).length ≤ (v.2 ++ [j]).length at hle
        have hneq : (List.ofFn u.2).length ≠ (v.2 ++ [j]).length := by
          intro heq
          exact hne (Prod.ext hanc.1 (hanc.2.eq_of_length heq))
        omega
      have hp : RootIndexed.IsAncestor (u.1, List.ofFn u.2) v := by
        refine ⟨hanc.1, ?_⟩
        exact List.prefix_of_prefix_length_le hanc.2 (List.prefix_append _ _)
          (by simp only [List.length_append, List.length_singleton] at hlt ⊢; omega)
      exact hv ⟨(u.1, List.ofFn u.2), Set.mem_singleton _, hp⟩
  · rw [← measurable_iff_comap_le]
    let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
      Tree.linePast initialInformation reproductionInformation {(u.1, List.ofFn u.2)}
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro k
      rw [measurable_pi_iff]
      intro p
      have hm := stateAt_measurable_singleton (S := S) (u.1, List.ofFn u.2)
        (p.1, List.ofFn p.2) (fun hanc => by
          apply Prod.ext hanc.1
          apply hanc.2.eq_of_length
          have hle := hanc.2.length_le
          simp only [List.length_ofFn] at hle ⊢
          have hk := Finset.mem_Iic.mp k.2
          omega)
      have heq : stateAt (S := S) (p.1, List.ofFn p.2) =
          (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S => x k.1 p) :=
        funext fun x => stateAt_ofFn x k.1 p
      rwa [heq] at hm
    · rw [measurable_pi_iff]
      intro q
      rw [measurable_pi_iff]
      intro v
      apply stateAt_measurable_singleton (u.1, List.ofFn u.2) (q.1.1, List.ofFn q.1.2 ++ v)
      intro hanc
      have huq : RootIndexed.IsAncestor (u.1, List.ofFn u.2) (q.1.1, List.ofFn q.1.2) := by
        refine ⟨hanc.1, ?_⟩
        exact List.prefix_of_prefix_length_le hanc.2 (List.prefix_append _ _)
          (by simp)
      have heq : u = q.1 := Prod.ext huq.1 (List.ofFn_injective
        (huq.2.eq_of_length (by simp)))
      exact False.elim (q.2 heq.symm)

end ProbabilityTheory.BranchingProcess.State

end
