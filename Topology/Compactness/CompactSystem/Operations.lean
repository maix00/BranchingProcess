/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Order.CountableSupClosed
public import Mathlib.Topology.Compactness.CompactSystem
public import Mathlib.Topology.Order.Compact
import Mathlib.Data.Nat.Pairing
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Compact-system operations

This file extends Mathlib's `IsCompactSystem` interface with generic compact
set-family constructions, products, countable-intersection, and finite-union
operations. The abstract closure, product, and transport results are useful independently
of analytic-set or capacity arguments; standard interval instances use the
general topology API.

## Public declarations

* `IsCompactSystem.image2_prod` sends compact systems
  `p` on `α` and `q` on `β` to the compact system
  `{s ×ˢ t | s ∈ p, t ∈ q}` on `α × β`.
* `IsCompactSystem.countableInfClosure` and `IsCompactSystem.supClosure`
  state that the countable-intersection and finite-union closures of a compact
  system remain compact systems.
* `IsCompactSystem.infClosure` derives the corresponding finite-intersection
  closure result.
* `IsCompactSystem.sigma` and `IsCompactSystem.sum` construct compact systems
  on dependent sums and binary sums; `IsCompactSystem.equiv` transports one
  along an equivalence.
* `IsCompactSystem.finsetCoe`, `isCompactSystem_singleton_empty`,
  `isCompactSystem_Icc`, and `isCompactSystem_insert_empty_Icc` give standard
  compact systems for finite sets and intervals.
* `IsCompactSystem.pi` states that the countable product
  of compact systems, with each coordinate allowed to use `univ`, is a compact
  system on the
  dependent function space.
-/

@[expose] public section

universe u

open Set CategoryTheory

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
  have hChoiceFin : ∀ k, Finite (Choice k) := fun k => (L k).finite_toSet.to_subtype
  have hPrefixFin : ∀ n, Finite (Prefix n) := by
    intro n
    let (k : Fin n) : Fintype (Choice k.val) := Fintype.ofFinite _
    let : Fintype ((k : Fin n) → Choice k.val) := inferInstance
    exact Finite.of_injective Subtype.val Subtype.val_injective
  have hPrefixNonempty : ∀ n, Nonempty (Prefix n) := by
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

/-- Finite intersections preserve compact systems. -/
protected theorem IsCompactSystem.infClosure {α : Type*} {p : Set (Set α)}
    (hp : IsCompactSystem p) : IsCompactSystem (infClosure p) := by
  refine hp.countableInfClosure.mono ?_
  exact infClosure_min subset_countableInfClosure infClosed_countableInfClosure


variable {𝓚 𝓚' : Type*} {ι : Type*}

lemma isCompactSystem_singleton_empty {α : Type*} : IsCompactSystem {(∅ : Set α)} :=
  fun C hC _ ↦ ⟨0, by simpa using hC 0⟩

lemma isCompactSystem_Icc (α : Type*) [TopologicalSpace α] [T2Space α] [Preorder α]
    [CompactIccSpace α] :
    IsCompactSystem {t | ∃ a b : α, Set.Icc a b = t} :=
  (isCompactSystem_isCompact _).mono fun _ ⟨_, _, heq⟩ ↦ heq ▸ isCompact_Icc

lemma isCompactSystem_insert_empty_Icc (α : Type*) [TopologicalSpace α] [T2Space α] [Preorder α]
    [CompactIccSpace α] :
    IsCompactSystem (insert ∅ {t | ∃ a b : α, Set.Icc a b = t}) := by
  refine (isCompactSystem_isCompact α).mono fun s hs ↦ ?_
  cases hs with
  | inl h => simp [h]
  | inr h => obtain ⟨_, _, heq⟩ := h; exact heq ▸ isCompact_Icc

/-- The set of Finset coercions forms a compact system. -/
lemma IsCompactSystem.finsetCoe :
    IsCompactSystem {t : Set 𝓚 | ∃ s : Finset 𝓚, (s : Set 𝓚) = t} := by
  let : TopologicalSpace 𝓚 := ⊥
  have : DiscreteTopology 𝓚 := ⟨rfl⟩
  apply IsCompactSystem.of_nonempty_iInter
  intro C hC hC_nonempty
  choose s hs using hC
  have hsub : ∀ n, Set.dissipate C n ⊆ (s 0 : Set 𝓚) :=
    fun n => (Set.antitone_dissipate (Nat.zero_le n)).trans
      (Set.dissipate_subset le_rfl |>.trans (by rw [← hs 0]))
  have h_compact : IsCompact (Set.dissipate C 0) :=
    (s 0).finite_toSet.subset (hsub 0) |>.isCompact
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (Set.dissipate C ·)
    (fun i => Set.antitone_dissipate (Nat.le_succ i))
    hC_nonempty h_compact
    (fun _ => isClosed_discrete _)
  simp only [Set.iInter_dissipate, Set.mem_iInter] at hx
  simp only [Set.nonempty_iInter]
  use x

/-- Transport a compact system along an equivalence of types. -/
lemma IsCompactSystem.equiv (e : 𝓚 ≃ 𝓚') {S : Set (Set 𝓚)} (hS : IsCompactSystem S) :
    IsCompactSystem {t : Set 𝓚' | e ⁻¹' t ∈ S} := by
  intro D hD hD_empty
  have h (s : Set 𝓚') : s = ∅ ↔ e ⁻¹' s = ∅ := by
    repeat rw [Set.eq_empty_iff_forall_notMem]
    refine ⟨fun h x => h (e x), fun h x hx => h (e.invFun x) (by simp [hx])⟩
  rw [h, Set.preimage_iInter] at hD_empty
  obtain ⟨N, hN⟩ := hS (fun i => e ⁻¹' D i) hD hD_empty
  rw [Set.dissipate, ← Set.preimage_iInter₂] at hN
  refine ⟨N, by rw [Set.dissipate, h, hN]⟩

private lemma iInter_sigma_eq_empty_iff {𝓚 : ι → Type*} {β : Type*} (s : β → Set ι)
    (f : β → (i : ι) → Set (𝓚 i)) :
     ⋂ b, (s b).sigma (f b) = ∅ ↔ ∀ i ∈ ⋂ b, s b, ⋂ b, f b i = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_iInter, Set.mem_sigma_iff]
  exact ⟨fun h i hi x hx => h ⟨i, x⟩ fun b => ⟨hi b, hx b⟩,
    fun h ⟨i, x⟩ hx => h i (fun b => (hx b).1) x (fun b => (hx b).2)⟩

/-- Variant with an additional condition `p b` (e.g. `b ≤ n` for `dissipate`). -/
private lemma iInter₂_sigma_eq_empty_iff {𝓚 : ι → Type*} {β : Type*} {p : β → Prop}
    (s : β → Set ι) (f : β → (i : ι) → Set (𝓚 i)) :
    ⋂ (b) (_ : p b), (s b).sigma (f b) = ∅ ↔
      ∀ i ∈ ⋂ (b) (_ : p b), s b, ⋂ (b) (_ : p b), f b i = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem, Set.mem_iInter, Set.mem_sigma_iff]
  exact ⟨fun h i hi x hx => h ⟨i, x⟩ fun b hb => ⟨hi b hb, hx b hb⟩,
    fun h ⟨i, x⟩ hx => h i (fun b hb => (hx b hb).1) x (fun b hb => (hx b hb).2)⟩

lemma IsCompactSystem.sigma {𝓚 : ι → Type*} {q : (i : ι) → Set (Set (𝓚 i))}
    (hq : ∀ i, IsCompactSystem (q i)) :
    IsCompactSystem {t : Set (Σ i, 𝓚 i) |
      ∃ s : Finset ι, t ∈ (s : Set ι).sigma '' (Set.univ.pi q)} := by
  classical
  intro C hC hC_empty
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ,
    forall_const] at hC
  choose s f hf hCfs using hC
  simp_rw [Set.dissipate, ← hCfs]
  simp_rw [← hCfs, iInter_sigma_eq_empty_iff] at hC_empty
  by_cases h : ⋂ b, (s b : Set ι) = ∅
  · obtain ⟨n₀, hn₀⟩ := IsCompactSystem.finsetCoe (fun b => (s b : Set ι))
      (fun b => ⟨s b, rfl⟩) h
    refine ⟨n₀, ?_⟩
    rw [Set.dissipate] at hn₀
    simp_rw [iInter₂_sigma_eq_empty_iff, hn₀]
    simp
  · have hs : (s 0).Nonempty := by
      rw [← Finset.coe_nonempty, Set.nonempty_iff_ne_empty]
      exact fun h0 => h <| Set.subset_eq_empty (Set.iInter_subset _ 0) h0
    obtain ⟨j₀, hj₀⟩ := hs
    classical
    have key₀ : ∀ j ∈ ⋂ b, s b, ∃ N,
        ⋂ (b ≤ N), f b j = ∅ := by
      intro j hj
      exact hq j (f · j) (fun i ↦ hf i j) (hC_empty j hj)
    have key₁ : ∀ j ∉ ⋂ b, s b, ∃ N, j ∉ s N := by
      intro j hj
      simpa [Set.mem_iInter, not_forall] using hj
    -- For each j ∈ s 0, find N(j) such that the fibre over j in the bounded sigma is empty.
    have key : ∀ j ∈ s 0, ∃ N,
        ∀ x, (⟨j, x⟩ : Σ k, 𝓚 k) ∉ ⋂ y, ⋂ (_ : y ≤ N), (s y : Set ι).sigma (f y) := by
      intro j _
      by_cases hjs : j ∈ ⋂ b, s b
      · obtain ⟨N, hN⟩ := key₀ j hjs
        refine ⟨N, fun x hx => ?_⟩
        have hxslice : x ∈ ⋂ b, ⋂ _ : b ≤ N, f b j := by
          simp only [Set.mem_iInter, Set.mem_sigma_iff] at hx ⊢
          exact fun b hb => (hx b hb).2
        rw [hN] at hxslice; exact hxslice
      · obtain ⟨b, hb⟩ := key₁ j hjs
        refine ⟨b, fun x hx => ?_⟩
        have : (⟨j, x⟩ : Σ k, 𝓚 k) ∈ (s b : Set ι).sigma (f b) :=
          (Set.mem_iInter.mp (Set.mem_iInter.mp hx b) le_rfl)
        exact hb (Finset.mem_coe.mp (Set.mem_sigma_iff.mp this).1)
    choose N hN using key
    use (s 0).attach.sup fun jh => N jh.val jh.prop
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨j, x⟩ hjx
    have hj0 : j ∈ s 0 := by
      have : (⟨j, x⟩ : Σ k, 𝓚 k) ∈ (s 0 : Set ι).sigma (f 0) :=
        Set.mem_iInter.mp (Set.mem_iInter.mp hjx 0) (Nat.zero_le _)
      exact Finset.mem_coe.mp (Set.mem_sigma_iff.mp this).1
    have hle : N j hj0 ≤ ((s 0).attach.sup fun jh => N jh.val jh.prop) :=
      Finset.le_sup (f := fun jh : { x // x ∈ s 0 } => N jh.val jh.prop)
        (Finset.mem_attach _ ⟨j, hj0⟩)
    exact hN j hj0 x
      (Set.iInter₂_mono' (fun b' j' => ⟨b', j'.trans hle, Set.Subset.rfl⟩) hjx)

/-- Sigma variant with fixed `s = Finset.univ`: subsystem of `IsCompactSystem.sigma`. -/
private lemma IsCompactSystem.sigma_ofFintype [Finite ι] {𝓚 : ι → Type*}
    {q : (i : ι) → Set (Set (𝓚 i))} (hq : ∀ i, IsCompactSystem (q i)) :
    IsCompactSystem (Set.univ.sigma '' (Set.univ.pi q)) := by
  have : Fintype ι := Fintype.ofFinite ι
  intro C hC hC_empty
  refine IsCompactSystem.sigma hq C (fun i => ?_) hC_empty
  obtain ⟨f, hf, hfC⟩ := hC i
  refine ⟨(Finset.univ : Finset ι), f, fun j _ => hf j (Set.mem_univ _), ?_⟩
  rw [Finset.coe_univ]; exact hfC

lemma IsCompactSystem.sum {𝓚 𝓚' : Type u} {q : Set (Set 𝓚)} {q' : Set (Set 𝓚')}
    (hq : IsCompactSystem q) (hq' : IsCompactSystem q') :
    IsCompactSystem {t | Sum.inl ⁻¹' t ∈ q ∧ Sum.inr ⁻¹' t ∈ q'} := by
  let Q : ∀ b : Bool, Set (Set (bif b then 𝓚' else 𝓚)) :=
    fun b => match b with | true => q' | false => q
  have hQ : ∀ b, IsCompactSystem (Q b) := fun b => by cases b <;> assumption
  have h_equiv := IsCompactSystem.equiv (Equiv.sumEquivSigmaBool 𝓚 𝓚').symm
    (IsCompactSystem.sigma_ofFintype hQ)
  convert h_equiv using 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun | true => Sum.inr ⁻¹' t | false => Sum.inl ⁻¹' t,
      fun | true => hr | false => hl,
      by ext ⟨b, x⟩; cases b <;> · simp [Equiv.sumEquivSigmaBool]⟩
  · rintro ⟨f, hf, hfC⟩
    have slice : ∀ b x, x ∈ f b ↔ (Equiv.sumEquivSigmaBool 𝓚 𝓚').symm ⟨b, x⟩ ∈ t :=
      fun b x => by simpa using Set.ext_iff.mp hfC ⟨b, x⟩
    constructor
    · specialize hf false
      simp only [Bool.cond_false] at hf
      convert hf using 1
      ext x
      exact (slice false x).symm
    · specialize hf true
      simp only [Bool.cond_true] at hf
      convert hf using 1
      ext x
      exact (slice true x).symm

end
