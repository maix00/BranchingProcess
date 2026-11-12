/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Combinatorics.Hall.Basic

/-!
# Finite matching from threshold counts

## Public declarations

- `Combinatorics.Matching.exists_injective_le_of_filter_card_le`: for finite
  sets `objectsToMatch` and `availablePartners`, if
  \[
  \#\{x\in\texttt{objectsToMatch}:\texttt{objectOrderKey}(x)\leq a\}
  \leq
  \#\{y\in\texttt{availablePartners}:\texttt{partnerOrderKey}(y)\leq a\}
  \]
  for every $a$, then an injection $\varphi$ exists with
  $\texttt{partnerOrderKey}(\varphi(x))\leq\texttt{objectOrderKey}(x)$.

The proof applies Mathlib's
`Fintype.all_card_le_filter_rel_iff_exists_injective` from
`Mathlib/Combinatorics/Hall/Basic.lean` to the relation
$g(q)\leq f(p)$.
-/

@[expose] public section

namespace Combinatorics.Matching

variable {Object Partner OrderKey : Type*}

/-- Threshold-count domination gives an injective matching from
`objectsToMatch` into `availablePartners`, with each partner's order key no
larger than the corresponding object's order key. The proof applies Hall's
theorem to the relation `partnerOrderKey q ≤ objectOrderKey p`. -/
theorem exists_injective_le_of_filter_card_le
    [DecidableEq Object] [DecidableEq Partner] [LinearOrder OrderKey]
    (objectOrderKey : Object → OrderKey) (partnerOrderKey : Partner → OrderKey)
    (objectsToMatch : Finset Object) (availablePartners : Finset Partner)
    (hthreshold : ∀ a : OrderKey,
      (objectsToMatch.filter fun p => objectOrderKey p ≤ a).card ≤
        (availablePartners.filter fun q => partnerOrderKey q ≤ a).card) :
    ∃ f : {p : Object // p ∈ objectsToMatch} → {q : Partner // q ∈ availablePartners},
      Function.Injective f ∧ ∀ p, partnerOrderKey (f p).1 ≤ objectOrderKey p.1 := by
  classical
  let matchingRelation :
      {p : Object // p ∈ objectsToMatch} →
        {q : Partner // q ∈ availablePartners} → Prop :=
    fun p q => partnerOrderKey q.1 ≤ objectOrderKey p.1
  have hHall : ∀ A : Finset {p : Object // p ∈ objectsToMatch},
      A.card ≤ (Finset.univ.filter fun q : {q : Partner // q ∈ availablePartners} =>
        ∃ p ∈ A, matchingRelation p q).card := by
    intro A
    by_cases hA : A.Nonempty
    · obtain ⟨pmax, hpmax, hmax⟩ :=
        Finset.exists_max_image A
          (fun p : {p : Object // p ∈ objectsToMatch} => objectOrderKey p.1) hA
      have hAtoObjectsToMatch : A.card ≤
          (objectsToMatch.filter fun p => objectOrderKey p ≤ objectOrderKey pmax.1).card := by
        apply Finset.card_le_card_of_injOn
          (fun p : {p : Object // p ∈ objectsToMatch} => p.1)
        · intro p hp
          exact Finset.mem_filter.mpr
            ⟨p.2, hmax p hp⟩
        · intro p _ q _ hpq
          exact Subtype.ext hpq
      have htoAvailablePartners := hthreshold (objectOrderKey pmax.1)
      have havailablePartnersToRelation :
          (availablePartners.filter fun q => partnerOrderKey q ≤ objectOrderKey pmax.1).card ≤
            (Finset.univ.filter fun q : {q : Partner // q ∈ availablePartners} =>
              ∃ p ∈ A, matchingRelation p q).card := by
        have hattach :
            (availablePartners.attach.filter fun q => partnerOrderKey q.1 ≤ objectOrderKey pmax.1).card =
              (availablePartners.filter fun q => partnerOrderKey q ≤ objectOrderKey pmax.1).card := by
          have h := congrArg Finset.card
            (Finset.filter_attach
              (fun q : Partner => partnerOrderKey q ≤ objectOrderKey pmax.1) availablePartners)
          simpa using h
        have huniv : availablePartners.attach = (Finset.univ : Finset {q : Partner // q ∈ availablePartners}) := by
          ext q
          simp
        rw [← hattach, huniv]
        apply Finset.card_le_card
        intro q hq
        obtain ⟨_, hqle⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨pmax, hpmax, hqle⟩⟩
      exact hAtoObjectsToMatch.trans
        (htoAvailablePartners.trans havailablePartnersToRelation)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
      simp
  obtain ⟨f, hinj, hrel⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective matchingRelation).mp hHall
  exact ⟨f, hinj, hrel⟩

end Combinatorics.Matching

end
