/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Basic.Survival.Basic
public import Combinatorics.Branching.Map
public import Combinatorics.BranchingWalk.Step.Selection.Count

/-!
# Generation sizes of a branching walk

For a branching walk `β`, `generationSize β n` is the extended cardinality
`(survivingParticlesAt β n).encard`. When the child-slot type is finite, each
generation is finite and `generationSize β n ≠ ⊤`; for a single-root walk,
`generationSize β 0 = 1` and
`generationSize β 1 = (β.step PUnit.unit []).childCount`.
`generationSlice_finite` and `generationSize_ne_top_of_finite_slots` give the
finite-generation conclusions. For a single-root walk,
`generationSize_zero` and `generationSize_one_eq_childCount` state the initial
values `Z₀ = 1` and `Z₁ = childCount(β.step PUnit.unit [])`, where
`Zₙ = generationSize β n`. The pathwise recursion
`generationSize_succ_eq_sum_childCount` is
`Z_(n+1) = ∑ p : {p // p ∈ survivingParticlesAt β n},
(β.step PUnit.unit p.1.2).childCount`.

`survivingParticlesAt_toBranching` and `generationSize_toBranching` state that
forgetting marks preserves the generation set and its size.
`generationSize_succ_eq_zero_of_eq_zero` proves `Zₙ = 0 → Z_(n+1) = 0`, and
`generationSize_eq_zero_of_le` proves `n ≤ m → Zₙ = 0 → Zₘ = 0`.
-/

@[expose] public section

namespace Combinatorics.Branching

private lemma finite_list_length_eq {α : Type*} [Finite α] (n : ℕ) :
    Finite {u : List α // u.length = n} := by
  classical
  refine Finite.of_injective
    (fun u : {u : List α // u.length = n} => fun i : Fin n => u.1[i]?) ?_
  intro u v h
  apply Subtype.ext
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < n
  · exact congrFun h ⟨i, hi⟩
  · rw [List.getElem?_eq_none_iff.mpr (by omega : u.1.length ≤ i),
      List.getElem?_eq_none_iff.mpr (by omega : v.1.length ≤ i)]

/-- The possibly infinite number of particles present at generation `n`,
across all labelled initial roots. -/
noncomputable def RootIndexed.BranchingWalk.generationSize
    {Root α Mark Position : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position)
    (n : ℕ) : ℕ∞ :=
  (survivingParticlesAt β n).encard

/-- Every fixed generation is finite when the child-slot type is finite.
This is a pathwise combinatorial fact, independent of the offspring law. -/
theorem RootIndexed.BranchingWalk.generationSlice_finite
    {α Mark Position : Type*} [Finite α]
    (β : _root_.Combinatorics.Branching.BranchingWalk α Mark Position) (n : ℕ) :
    (survivingParticlesAt β n).Finite := by
  classical
  have hlist : Finite {u : List α // u.length = n} := finite_list_length_eq n
  have hlevel : Finite
      {p : Combinatorics.UlamHarris.RootIndexed.TreeNode PUnit.{1} α //
        p.2.length = n} := by
    refine @Finite.of_injective _ _ hlist
      (fun p => (⟨p.1.2, p.2⟩ : {u : List α // u.length = n})) ?_
    intro p q hpq
    apply Subtype.ext
    have haddr : p.1.2 = q.1.2 := congrArg Subtype.val hpq
    exact Prod.ext (Subsingleton.elim _ _) haddr
  have hslice : Finite
      {p : Combinatorics.UlamHarris.RootIndexed.TreeNode PUnit.{1} α //
        p ∈ survivingParticlesAt β n} := by
    refine @Finite.of_injective _ _ hlevel
      (fun p => (⟨p.1, by
        simpa [Combinatorics.UlamHarris.RootIndexed.generation] using p.2.2⟩ :
        {p : Combinatorics.UlamHarris.RootIndexed.TreeNode PUnit.{1} α //
          p.2.length = n})) ?_
    intro p q hpq
    exact Subtype.ext (congrArg
      (fun q : {p : Combinatorics.UlamHarris.RootIndexed.TreeNode PUnit.{1} α //
          p.2.length = n} => q.1) hpq)
  exact Set.finite_coe_iff.mpr hslice

/-- With finitely many child slots, the extended generation count is always
finite. -/
theorem RootIndexed.BranchingWalk.generationSize_ne_top_of_finite_slots
    {α Mark Position : Type*} [Finite α]
    (β : _root_.Combinatorics.Branching.BranchingWalk α Mark Position) (n : ℕ) :
    β.generationSize n ≠ ⊤ := by
  unfold RootIndexed.BranchingWalk.generationSize
  exact Set.encard_ne_top_iff.mpr
    (RootIndexed.BranchingWalk.generationSlice_finite β n)

/-- A single-root branching walk has exactly its initial particle in
generation zero. -/
theorem RootIndexed.BranchingWalk.generationSize_zero
    {α Mark Position : Type*}
    (β : _root_.Combinatorics.Branching.BranchingWalk α Mark Position) :
    β.generationSize 0 = 1 := by
  classical
  rw [RootIndexed.BranchingWalk.generationSize]
  have hslice :
      survivingParticlesAt β 0 =
        {(PUnit.unit, ([] : Combinatorics.UlamHarris.TreeNode α))} := by
    ext p
    rcases p with ⟨r, u⟩
    cases r
    rw [mem_survivingParticlesAt_iff,
      mem_survivingParticles_iff_surviveAlong]
    simp [Combinatorics.UlamHarris.generation]
    intro hu
    subst u
    exact surviveAlong_nil _ _
  rw [hslice, Set.encard_singleton]

/-- The particles present at generation one correspond exactly to the
children in a single root's first offspring configuration. -/
theorem RootIndexed.BranchingWalk.generationSize_one_eq_childCount
    {α Mark Position : Type*}
    (β : _root_.Combinatorics.Branching.BranchingWalk α Mark Position) :
    β.generationSize 1 = (β.step PUnit.unit []).childCount := by
  classical
  rw [RootIndexed.BranchingWalk.generationSize]
  change (survivingParticlesAt β 1).encard =
    (support (β.step PUnit.unit [])).encard
  let e :
      {i // i ∈ support (β.step PUnit.unit [])} ≃
    {p // p ∈ survivingParticlesAt β 1} := {
    toFun := fun i => ⟨(PUnit.unit, [i.1]), by
      rw [mem_survivingParticlesAt_iff]
      constructor
      · rw [mem_survivingParticles_iff_surviveAlong]
        rw [surviveAlong_cons]
        exact ⟨i.2, surviveAlong_nil _ _⟩
      · simp [Combinatorics.UlamHarris.generation]
    ⟩
    invFun := fun p => by
      rcases p with ⟨⟨r, u⟩, hp⟩
      cases r
      have hlen : u.length = 1 := by
        simpa [Combinatorics.UlamHarris.generation] using hp.2
      have hsurvive :=
        (mem_survivingParticles_iff_surviveAlong β PUnit.unit u).mp hp.1
      have hu : u = [u[0]'(by omega)] := by
        obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hlen
        simp [hi]
      rw [hu, surviveAlong_cons] at hsurvive
      exact ⟨u[0]'(by omega), hsurvive.1⟩
    left_inv := fun i => by
      apply Subtype.ext
      rfl
    right_inv := fun p => by
      apply Subtype.ext
      rcases p with ⟨⟨r, u⟩, hp⟩
      cases r
      have hlen : u.length = 1 := by
        simpa [Combinatorics.UlamHarris.generation] using hp.2
      have hu : u = [u[0]'(by omega)] := by
        obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hlen
        simp [hi]
      exact Prod.ext rfl hu.symm
  }
  exact (Set.encard_congr e).symm

/-- In a single-root walk with finitely many child slots, the next generation is
the disjoint union of the offspring configurations attached to the current
generation. This is the pathwise Galton--Watson recursion, before taking any
expectations. -/
theorem BranchingWalk.generationSize_succ_eq_sum_childCount
    {α Mark Position : Type*} [Finite α]
    (β : BranchingWalk α Mark Position) (n : ℕ) :
    letI : Fintype {p // p ∈ survivingParticlesAt β n} :=
      (RootIndexed.BranchingWalk.generationSlice_finite β n).fintype
    β.generationSize (n + 1) =
      ∑ p : {p // p ∈ survivingParticlesAt β n},
        (β.step PUnit.unit p.1.2).childCount := by
  classical
  let P := {p // p ∈ survivingParticlesAt β n}
  let Q := {p // p ∈ survivingParticlesAt β (n + 1)}
  let C (p : P) :=
    {i : α // survive (β.step PUnit.unit p.1.2) i}
  have hPfin : (survivingParticlesAt β n).Finite :=
    RootIndexed.BranchingWalk.generationSlice_finite β n
  have hQfin : (survivingParticlesAt β (n + 1)).Finite :=
    RootIndexed.BranchingWalk.generationSlice_finite β (n + 1)
  letI : Fintype P := hPfin.fintype
  letI : Fintype Q := hQfin.fintype
  letI : ∀ p : P, Fintype (C p) := fun p => Fintype.ofFinite (C p)
  have hcastVal {p q : P} (h : p = q) (x : C p) :
      (h ▸ x).val = x.val := by
    cases h
    rfl
  let forward : (Σ p : P, C p) → Q := fun z => by
    rcases z with ⟨⟨⟨r, u⟩, hp⟩, ⟨i, hi⟩⟩
    cases r
    have hp' := (mem_survivingParticlesAt_iff β n (PUnit.unit, u)).mp hp
    have hparent : surviveAlong (β.step PUnit.unit) [] u :=
      (mem_survivingParticles_iff_surviveAlong β PUnit.unit u).mp hp'.1
    refine ⟨(PUnit.unit, u ++ [i]), ?_⟩
    rw [mem_survivingParticlesAt_iff,
      mem_survivingParticles_iff_surviveAlong]
    constructor
    · rw [surviveAlong_root_append_singleton_iff]
      exact ⟨hparent, hi⟩
    · have hlen : u.length = n := by
        simpa [Combinatorics.UlamHarris.generation] using hp'.2
      simp [Combinatorics.UlamHarris.generation, hlen]
  let backward : Q → (Σ p : P, C p) := fun q => by
    rcases q with ⟨⟨r, u⟩, hq⟩
    cases r
    have hlen : u.length = n + 1 := by
      simpa [Combinatorics.UlamHarris.generation] using hq.2
    have hidx : n < u.length := by omega
    have hsurvive : surviveAlong (β.step PUnit.unit) [] u :=
      (mem_survivingParticles_iff_surviveAlong β PUnit.unit u).mp
        ((mem_survivingParticlesAt_iff β (n + 1) (PUnit.unit, u)).mp hq).1
    have hparent : surviveAlong (β.step PUnit.unit) [] (u.take n) := by
      apply surviveAlong_prefix (β.step PUnit.unit) (u.take n) (u.drop n)
      rw [List.take_append_drop]
      exact hsurvive
    have hchild : survive (β.step PUnit.unit (u.take n)) u[n] :=
      (surviveAlong_root_iff_forall_fin (β.step PUnit.unit) u).mp hsurvive
        ⟨n, hidx⟩
    refine ⟨⟨(PUnit.unit, u.take n), ?_⟩, ⟨u[n], hchild⟩⟩
    rw [mem_survivingParticlesAt_iff,
      mem_survivingParticles_iff_surviveAlong]
    exact ⟨hparent, by simp [Combinatorics.UlamHarris.generation, hlen]⟩
  let e : (Σ p : P, C p) ≃ Q := {
    toFun := forward
    invFun := backward
    left_inv := by
      intro z
      rcases z with ⟨⟨⟨r, u⟩, hp⟩, ⟨i, hi⟩⟩
      cases r
      have hlen : u.length = n := by
        simpa [Combinatorics.UlamHarris.generation] using
          (mem_survivingParticlesAt_iff β n (PUnit.unit, u)).mp hp |>.2
      let z' : Σ p : P, C p := ⟨⟨(PUnit.unit, u), hp⟩, ⟨i, hi⟩⟩
      have hbase : (backward (forward z')).1 = z'.1 := by
        dsimp [backward, forward]
        apply Subtype.ext
        change (PUnit.unit, (u ++ [i]).take n) = (PUnit.unit, u)
        apply Prod.ext
        · rfl
        · simp [hlen]
      change backward (forward z') = z'
      refine Sigma.ext hbase ?_
      have hval : (backward (forward z')).2.val = z'.2.val := by
        dsimp [backward, forward, z']
        simp [List.getElem_append_right, hlen]
      have hcast : hbase ▸ (backward (forward z')).2 = z'.2 := by
        apply Subtype.ext
        calc
          (hbase ▸ (backward (forward z')).2).val =
              (backward (forward z')).2.val := hcastVal hbase _
          _ = z'.2.val := hval
      exact (eqRec_heq hbase (backward (forward z')).2).symm.trans
        (heq_of_eq hcast)
    right_inv := by
      intro q
      rcases q with ⟨⟨r, u⟩, hq⟩
      cases r
      have hlen : u.length = n + 1 := by
        simpa [Combinatorics.UlamHarris.generation] using hq.2
      have hidx : n < u.length := by omega
      apply Subtype.ext
      dsimp [backward, forward]
      change (PUnit.unit, u.take n ++ [u[n]]) = (PUnit.unit, u)
      apply Prod.ext
      · rfl
      · calc
          u.take n ++ [u[n]] = u.take (n + 1) := List.take_concat_get' u n hidx
          _ = u := by simp [hlen]
  }
  have hgen :
      β.generationSize (n + 1) = (Fintype.card Q : ℕ∞) := by
    unfold RootIndexed.BranchingWalk.generationSize
    rw [← Set.coe_fintypeCard (survivingParticlesAt β (n + 1))]
  have hchild (p : P) :
      (β.step PUnit.unit p.1.2).childCount = (Fintype.card (C p) : ℕ∞) := by
    letI : Fintype (Combinatorics.Branching.support
        (β.step PUnit.unit p.1.2)) :=
      Fintype.ofFinite _
    unfold Combinatorics.Branching.Step.childCount
    rw [← Set.coe_fintypeCard (Combinatorics.Branching.support
      (β.step PUnit.unit p.1.2))]
    rfl
  calc
    β.generationSize (n + 1) = (Fintype.card Q : ℕ∞) := hgen
    _ = (Fintype.card (Σ p : P, C p) : ℕ∞) := by
      exact_mod_cast Fintype.card_congr e.symm
    _ = ∑ p : P, (Fintype.card (C p) : ℕ∞) := by
      simp [Fintype.card_sigma]
    _ = ∑ p : P, (β.step PUnit.unit p.1.2).childCount := by
      simp_rw [hchild]

/-- Forgetting marks does not change the surviving population at any
generation. -/
@[simp] theorem RootIndexed.BranchingWalk.survivingParticlesAt_toBranching
    {Root α Mark Position : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position) (n : ℕ) :
    survivingParticlesAt β.toBranching n = survivingParticlesAt β n := by
  ext p
  rw [mem_survivingParticlesAt_iff, mem_survivingParticlesAt_iff]
  apply and_congr
  · rw [mem_survivingParticles_iff_surviveAlong,
      mem_survivingParticles_iff_surviveAlong]
    exact RootIndexed.BranchingWalk.surviveAlong_toBranching_iff
      β p.1 [] p.2
  · rfl

/-- Forgetting marks does not alter generation sizes. -/
@[simp] theorem RootIndexed.BranchingWalk.generationSize_toBranching
    {Root α Mark Position : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position) (n : ℕ) :
    β.toBranching.generationSize n = β.generationSize n := by
  simp [RootIndexed.BranchingWalk.generationSize]

/- Once a generation is empty, its children are absent, so all later
generations are empty as well. -/
theorem RootIndexed.BranchingWalk.generationSize_succ_eq_zero_of_eq_zero
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) (n : ℕ)
    (hzero : β.generationSize n = 0) :
    β.generationSize (n + 1) = 0 := by
  change (survivingParticlesAt β n).encard = 0 at hzero
  have hempty : survivingParticlesAt β n = ∅ :=
    Set.encard_eq_zero.mp hzero
  change (survivingParticlesAt β (n + 1)).encard = 0
  apply Set.encard_eq_zero.mpr
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rcases p with ⟨r, u⟩
  rw [mem_survivingParticlesAt_iff,
    mem_survivingParticles_iff_surviveAlong] at hp
  have hu : u.length = n + 1 := by
    simpa [Combinatorics.UlamHarris.generation] using hp.2
  have hprefixLength : (u.take n).length = n := by
    rw [List.length_take, hu, Nat.min_eq_left]
    omega
  have hsurvive : surviveAlong (β.step r) [] u := hp.1
  have hprefixSurvives : surviveAlong (β.step r) [] (u.take n) := by
    apply surviveAlong_prefix (β.step r) (u.take n) (u.drop n)
    rw [List.take_append_drop]
    exact hsurvive
  have hparent : (r, u.take n) ∈ survivingParticlesAt β n := by
    rw [mem_survivingParticlesAt_iff,
      mem_survivingParticles_iff_surviveAlong]
    refine ⟨hprefixSurvives, ?_⟩
    change (u.take n).length = n
    exact hprefixLength
  rw [hempty] at hparent
  exact hparent

/-- An empty generation forces every later generation to be empty. -/
theorem RootIndexed.BranchingWalk.generationSize_eq_zero_of_le
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) {n m : ℕ}
    (hnm : n ≤ m) (hzero : β.generationSize n = 0) :
    β.generationSize m = 0 := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      simpa using hzero
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · have hmid : β.generationSize m = 0 := ih hnm' hzero
        simpa using
          RootIndexed.BranchingWalk.generationSize_succ_eq_zero_of_eq_zero
            β m hmid
      · have hn : n = m + 1 := by omega
        subst n
        exact hzero

end Combinatorics.Branching

end
