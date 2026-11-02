/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Combinatorics.Hall.Basic

/-!
# Finite monotone matching from lower-tail counts

## Public declarations

- `Combinatorics.Matching.exists_injective_le_of_filter_card_le`: for finite
  candidate populations $S$ and $T$ in linearly ordered value spaces, if
  $|\{p\in S:f(p)\leq a\}|\leq|\{q\in T:g(q)\leq a\}|$ for every $a$,
  then there is an injective map $\varphi:S\to T$ with
  $g(\varphi(p))\leq f(p)$ for every $p\in S$.

The proof applies Mathlib's
`Fintype.all_card_le_filter_rel_iff_exists_injective` from
`Mathlib/Combinatorics/Hall/Basic.lean` to the relation $g(q)\leq f(p)$.
-/

@[expose] public section

namespace Combinatorics.Matching

variable {Source Target Value : Type*}

/-- Lower-tail count domination gives an injective matching from the source
population to the target population, with each matched target value no larger
than its source value. This is an application of Hall's theorem to the relation
`targetValue q ≤ sourceValue p`. -/
theorem exists_injective_le_of_filter_card_le
    [DecidableEq Source] [DecidableEq Target] [LinearOrder Value]
    (sourceValue : Source → Value) (targetValue : Target → Value)
    (source : Finset Source) (target : Finset Target)
    (hthreshold : ∀ a : Value,
      (source.filter fun p => sourceValue p ≤ a).card ≤
        (target.filter fun q => targetValue q ≤ a).card) :
    ∃ f : {p : Source // p ∈ source} → {q : Target // q ∈ target},
      Function.Injective f ∧ ∀ p, targetValue (f p).1 ≤ sourceValue p.1 := by
  classical
  let r : {p : Source // p ∈ source} → {q : Target // q ∈ target} → Prop :=
    fun p q => targetValue q.1 ≤ sourceValue p.1
  have hHall : ∀ A : Finset {p : Source // p ∈ source},
      A.card ≤ (Finset.univ.filter fun q : {q : Target // q ∈ target} =>
        ∃ p ∈ A, r p q).card := by
    intro A
    by_cases hA : A.Nonempty
    · obtain ⟨pmax, hpmax, hmax⟩ :=
        Finset.exists_max_image A
          (fun p : {p : Source // p ∈ source} => sourceValue p.1) hA
      have hAtoSource : A.card ≤
          (source.filter fun p => sourceValue p ≤ sourceValue pmax.1).card := by
        apply Finset.card_le_card_of_injOn
          (fun p : {p : Source // p ∈ source} => p.1)
        · intro p hp
          exact Finset.mem_filter.mpr
            ⟨p.2, hmax p hp⟩
        · intro p _ q _ hpq
          exact Subtype.ext hpq
      have htoTarget := hthreshold (sourceValue pmax.1)
      have htargetToRel :
          (target.filter fun q => targetValue q ≤ sourceValue pmax.1).card ≤
            (Finset.univ.filter fun q : {q : Target // q ∈ target} =>
              ∃ p ∈ A, r p q).card := by
        have hattach :
            (target.attach.filter fun q => targetValue q.1 ≤ sourceValue pmax.1).card =
              (target.filter fun q => targetValue q ≤ sourceValue pmax.1).card := by
          have h := congrArg Finset.card
            (Finset.filter_attach
              (fun q : Target => targetValue q ≤ sourceValue pmax.1) target)
          simpa using h
        have huniv : target.attach = (Finset.univ : Finset {q : Target // q ∈ target}) := by
          ext q
          simp
        rw [← hattach, huniv]
        apply Finset.card_le_card
        intro q hq
        obtain ⟨_, hqle⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨pmax, hpmax, hqle⟩⟩
      exact hAtoSource.trans (htoTarget.trans htargetToRel)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
      simp
  obtain ⟨f, hinj, hrel⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hHall
  exact ⟨f, hinj, hrel⟩

end Combinatorics.Matching

end
