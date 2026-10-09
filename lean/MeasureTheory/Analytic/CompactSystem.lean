/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Data.Nat.Pairing
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Order.CountableSupClosed
public import Mathlib.Topology.Compactness.CompactSystem

/-!
# Compact-system closure lemmas for analytic projections

This file develops axiom-clean compact-system closure facts needed by a local
Choquet-capacitability proof.  It does not import the BrownianMotion Choquet
development.
-/

@[expose] public section

universe u

open Set CategoryTheory

namespace MeasureTheory.Analytic

/-- The product of two compact systems of sets is a compact system. -/
theorem IsCompactSystem.image2_prod {α β : Type*}
    {p : Set (Set α)} {q : Set (Set β)}
    (hp : IsCompactSystem p) (hq : IsCompactSystem q) :
    IsCompactSystem (Set.image2 (· ×ˢ ·) p q) := by
  classical
  intro C hC hCempty
  simp only [Set.mem_image2] at hC
  choose A hA B hB hAB using hC
  by_cases hAempty : (⋂ n, A n) = ∅
  · obtain ⟨N, hN⟩ := hp A hA hAempty
    refine ⟨N, Set.eq_empty_iff_forall_notMem.2 ?_⟩
    intro z hz
    have hzA : z.1 ∈ Set.dissipate A N := by
      rw [Set.dissipate_def]
      simp only [Set.mem_iInter]
      intro n hn
      have hzC : z ∈ Set.dissipate C N := hz
      rw [Set.dissipate_def] at hzC
      simp only [Set.mem_iInter] at hzC
      have hzCn : z ∈ C n := hzC n hn
      rw [← hAB n] at hzCn
      exact hzCn.1
    rw [hN] at hzA
    exact hzA
  · have hAne : (⋂ n, A n).Nonempty := Set.nonempty_iff_ne_empty.mpr hAempty
    obtain ⟨x, hx⟩ := hAne
    have hBempty : (⋂ n, B n) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro y hy
      have hxy : (x, y) ∈ ⋂ n, C n := by
        simp only [Set.mem_iInter]
        intro n
        rw [← hAB n]
        exact ⟨Set.mem_iInter.1 hx n, Set.mem_iInter.1 hy n⟩
      exact Set.notMem_empty _ (hCempty ▸ hxy)
    obtain ⟨N, hN⟩ := hq B hB hBempty
    refine ⟨N, Set.eq_empty_iff_forall_notMem.2 ?_⟩
    intro z hz
    have hzB : z.2 ∈ Set.dissipate B N := by
      rw [Set.dissipate_def]
      simp only [Set.mem_iInter]
      intro n hn
      have hzC : z ∈ Set.dissipate C N := hz
      rw [Set.dissipate_def] at hzC
      simp only [Set.mem_iInter] at hzC
      have hzCn : z ∈ C n := hzC n hn
      rw [← hAB n] at hzCn
      exact hzCn.2
    rw [hN] at hzB
    exact hzB

/-- A countable intersection closure of a compact system is a compact system. -/
theorem IsCompactSystem.countableInfClosure {α : Type*} {p : Set (Set α)}
    (hp : IsCompactSystem p) :
    IsCompactSystem (countableInfClosure p) := by
  classical
  intro C hC hCempty
  simp_rw [mem_countableInfClosure_iff_iInf] at hC
  choose A hA hCeq using hC
  let D : ℕ → Set α := fun j => A j.unpair.1 j.unpair.2
  have hD : ∀ j, D j ∈ p := fun j => hA j.unpair.1 j.unpair.2
  have hDempty : (⋂ j, D j) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hxC : x ∈ ⋂ i, C i := by
      simp only [Set.mem_iInter]
      intro i
      rw [← hCeq i]
      change x ∈ (⋂ j, A i j)
      rw [Set.mem_iInter]
      intro j
      simpa [D] using Set.mem_iInter.1 hx (Nat.pair i j)
    exact Set.notMem_empty _ (hCempty ▸ hxC)
  obtain ⟨N, hN⟩ := hp D hD hDempty
  refine ⟨N, Set.eq_empty_iff_forall_notMem.2 ?_⟩
  intro x hx
  have hxC : ∀ i ≤ N, x ∈ C i := by
    simpa only [Set.dissipate_def, Set.mem_iInter] using hx
  have hxD : ∀ j ≤ N, x ∈ D j := by
    intro j hj
    have hi : j.unpair.1 ≤ N := j.unpair_left_le.trans hj
    have hxCi := hxC j.unpair.1 hi
    rw [← hCeq] at hxCi
    change x ∈ (⋂ n, A j.unpair.1 n) at hxCi
    exact Set.mem_iInter.1 hxCi j.unpair.2
  have hx' : x ∈ Set.dissipate D N := by
    simpa only [Set.dissipate_def, Set.mem_iInter] using hxD
  rw [hN] at hx'
  exact hx'

/-- A countable product of compact systems is a compact system. -/
theorem IsCompactSystem.pi {K : ℕ → Type*} {q : (n : ℕ) → Set (Set (K n))}
    (hq : ∀ n, IsCompactSystem (q n)) :
    IsCompactSystem (Set.univ.pi '' Set.univ.pi (fun n ↦ insert Set.univ (q n))) := by
  classical
  intro C hC hCempty
  simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const] at hC
  choose f hf hCeq using hC
  have hcoord : ∃ j, (⋂ n, f n j) = ∅ := by
    by_contra hnone
    push Not at hnone
    let x : (n : ℕ) → K n := fun j => Classical.choose (hnone j)
    have hxcoord : ∀ j, x j ∈ ⋂ n, f n j := fun j => Classical.choose_spec (hnone j)
    have hx : x ∈ ⋂ n, C n := by
      apply Set.mem_iInter.mpr
      intro n
      rw [← hCeq n]
      apply Set.mem_univ_pi.mpr
      intro j
      exact Set.mem_iInter.mp (hxcoord j) n
    exact Set.notMem_empty _ (hCempty ▸ hx)
  obtain ⟨j, hj⟩ := hcoord
  have hqj : IsCompactSystem (insert Set.univ (q j)) := (hq j).insert_univ
  obtain ⟨N, hN⟩ := hqj (fun n => f n j) (fun n => hf n j) hj
  refine ⟨N, Set.eq_empty_iff_forall_notMem.2 ?_⟩
  intro x hx
  have hxC : ∀ n ≤ N, x ∈ C n := by
    simpa only [Set.dissipate_def, Set.mem_iInter] using hx
  have hxj : x j ∈ Set.dissipate (fun n => f n j) N := by
    rw [Set.mem_dissipate]
    intro n hn
    have hxCn : x ∈ C n := hxC n hn
    rw [← hCeq n] at hxCn
    exact Set.mem_univ_pi.mp hxCn j
  rw [hN] at hxj
  exact hxj

/-- Finite unions preserve compact systems.  The proof uses Mathlib's finite inverse-system
compactness theorem: compatible finite choices of a component at each level give one component
sequence whose every finite intersection is nonempty. -/
theorem IsCompactSystem.supClosure {α : Type u} {p : Set (Set α)}
    (hp : IsCompactSystem p) : IsCompactSystem (supClosure p) := by
  classical
  intro C hC hCempty
  choose L hLne hLsub hLsup using hC
  have hCeq : ∀ n, C n = ⋃₀ (L n : Set (Set α)) := by
    intro n
    rw [← hLsup n, ← Finset.sup_id_set_eq_sUnion, Finset.sup'_eq_sup]
  by_contra hno
  push Not at hno
  have hdis : ∀ n, (Set.dissipate C n).Nonempty := hno
  let Choice : ℕ → Type u := fun k => {s : Set α // s ∈ (L k : Set (Set α))}
  let Prefix : ℕ → Type u := fun n =>
    {f : (k : Fin n) → Choice k.val // ∃ x : α, ∀ k, x ∈ (f k).val}
  haveI hChoiceFin : ∀ k, Finite (Choice k) := fun k => (L k).finite_toSet.to_subtype
  haveI hPrefixFin : ∀ n, Finite (Prefix n) := by
    intro n
    letI (k : Fin n) : Fintype (Choice k.val) := Fintype.ofFinite _
    letI : Fintype ((k : Fin n) → Choice k.val) := inferInstance
    exact Finite.of_injective Subtype.val Subtype.val_injective
  haveI hPrefixNonempty : ∀ n, Nonempty (Prefix n) := by
    intro n
    obtain ⟨x, hx⟩ := hdis n
    have hx' : ∀ i ≤ n, x ∈ C i := by
      simpa only [Set.dissipate_def, Set.mem_iInter] using hx
    have hmem (k : Fin n) : ∃ s : Set α, s ∈ (L k.val : Set (Set α)) ∧ x ∈ s := by
      have hk := hx' k.val (Nat.le_of_lt k.isLt)
      rw [hCeq k.val, Set.mem_sUnion] at hk
      exact hk
    let f : (k : Fin n) → Choice k.val := fun k =>
      ⟨Classical.choose (hmem k), (Classical.choose_spec (hmem k)).1⟩
    refine ⟨⟨f, x, ?_⟩⟩
    intro k
    exact (Classical.choose_spec (hmem k)).2
  let F : ℕᵒᵖ ⥤ Type u :=
    { obj n := Prefix n.unop
      map := fun {i j} f =>
        TypeCat.ofHom (fun (g : Prefix i.unop) =>
          ⟨fun k => g.1 ⟨k.val, Nat.lt_of_lt_of_le k.isLt (CategoryTheory.leOfHom f.unop)⟩,
            by
              obtain ⟨x, hx⟩ := g.2
              exact ⟨x, fun k => hx ⟨k.val, Nat.lt_of_lt_of_le k.isLt
                (CategoryTheory.leOfHom f.unop)⟩⟩⟩)
      map_id := by
        intro i
        ext g k
        rfl
      map_comp := by
        intro i j k f g
        ext s n
        rfl }
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  let D : ℕ → Set α := fun k =>
    ((u (Opposite.op (k + 1))).val
      ⟨k, by simpa only [Opposite.unop_op] using Nat.lt_succ_self k⟩).val
  have hD : ∀ k, D k ∈ p := by
    intro k
    exact hLsub k ((u (Opposite.op (k + 1))).val
      ⟨k, by simpa only [Opposite.unop_op] using Nat.lt_succ_self k⟩).property
  have hDfinite : ∀ n, (Set.dissipate D n).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := (u (Opposite.op (n + 1))).property
    refine ⟨x, ?_⟩
    rw [Set.mem_dissipate]
    intro k hk
    let e : Opposite.op (n + 1) ⟶ Opposite.op (k + 1) :=
      (CategoryTheory.homOfLE (show k + 1 ≤ n + 1 by omega)).op
    have hcoh := hu e
    have hevalChoice : ((u (Opposite.op (n + 1))).val
          ⟨k, by simpa only [Opposite.unop_op] using Nat.lt_succ_of_le hk⟩) =
        ((u (Opposite.op (k + 1))).val
          ⟨k, by simpa only [Opposite.unop_op] using Nat.lt_succ_self k⟩) := by
      have h := congrArg (fun z : Prefix (k + 1) => z.val
        ⟨k, by simpa only [Opposite.unop_op] using Nat.lt_succ_self k⟩) hcoh
      simpa [F] using h
    have heval := congrArg Subtype.val hevalChoice
    change x ∈ ((u (Opposite.op (k + 1))).val
      ⟨k, by simpa only [Opposite.unop_op] using Nat.lt_succ_self k⟩).val
    rw [← heval]
    exact hx ⟨k, by simpa only [Opposite.unop_op] using Nat.lt_succ_of_le hk⟩
  obtain ⟨x, hx⟩ := hp.nonempty_iInter hD hDfinite
  have hxC : x ∈ ⋂ n, C n := by
    simp only [Set.mem_iInter]
    intro n
    rw [hCeq n, Set.mem_sUnion]
    exact ⟨D n, ((u (Opposite.op (n + 1))).val
      ⟨n, by simpa only [Opposite.unop_op] using Nat.lt_succ_self n⟩).property,
      Set.mem_iInter.1 hx n⟩
  exact Set.notMem_empty _ (hCempty ▸ hxC)

end MeasureTheory.Analytic

end
