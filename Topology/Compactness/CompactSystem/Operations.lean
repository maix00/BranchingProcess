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

For compact systems `p` on `α` and `q` on `β`, their product family is compact;
countable intersections and finite unions preserve compactness:

\[
\begin{aligned}
\operatorname{IsCompactSystem}(p)\land\operatorname{IsCompactSystem}(q)
&\Longrightarrow
\operatorname{IsCompactSystem}\{A\times B:A\in p,\ B\in q\},\\
\operatorname{IsCompactSystem}(p)
&\Longrightarrow
\operatorname{IsCompactSystem}(\operatorname{countableInfClosure}(p))\land
\operatorname{IsCompactSystem}(\operatorname{supClosure}(p)).
\end{aligned}
\]

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

end
