/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/
module

public import MeasureTheory.Analytic.Paving.Basic
import Topology.Compactness.CompactSystem.Operations

import all MeasureTheory.Analytic.Paving.Lemmas.FiniteUnion
import Mathlib.Order.SetDissipate

/-!
# Projection of antitone sequences of finite product unions

## Public declarations

For an antitone sequence of finite product unions in the stated compact
system, projection commutes with countable intersection:

\[
\{\operatorname{fst}(x)\mid x\in\bigcap_{n\in\mathbb N}B_n\}
=\bigcap_{n\in\mathbb N}\{\operatorname{fst}(x)\mid x\in B_n\}.
\]

- `Paving.fst_iInter_of_supClosure_image2_prod_of_antitone`: assume `∅ ∈ q`,
  `q` is a compact system, `B : ℕ → Set (𝓧 × 𝓚)` is antitone, and
  `B n ∈ supClosure (Set.image2 (· ×ˢ ·) p q)` for every `n`. Then
  `Prod.fst '' (⋂ n, B n) = ⋂ n, Prod.fst '' B n`.

The finite-natural-index closure representation is kept in the internal
`Paving/Lemmas/` subtree; the finite-union gluing steps remain private to this
proof. The capacity application and its source references are recorded in
`MeasureTheory.Analytic.Capacity.Projection`.
-/

@[expose] public section

open Set

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓚 : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}

private lemma finset_iUnion_mem_supClosure {s : Finset ℕ} (hs_nonempty : s.Nonempty)
    {A : ℕ → Set 𝓧} (hs : ∀ n ∈ s, A n ∈ p) :
    (⋃ n ∈ s, A n) ∈ supClosure p := by
  rw [mem_supClosure_set_iff_natIndexedUnion]
  exact ⟨s, hs_nonempty, A, hs, rfl⟩

private lemma finset_iUnion_mem_supClosure_of_supClosure {s : Finset ℕ} (hs_nonempty : s.Nonempty) {A : ℕ → Set 𝓧}
    (hs : ∀ n ∈ s, A n ∈ supClosure p) :
    (⋃ n ∈ s, A n) ∈ supClosure p := by
  have := finset_iUnion_mem_supClosure hs_nonempty hs
  rwa [supClosure_idem] at this

/-- For a compact system in the second coordinate, projection onto the first
coordinate commutes with countable intersections of antitone sequences of
finite unions of product sets. -/
lemma fst_iInter_of_supClosure_image2_prod_of_antitone (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q)
    {B : ℕ → Set (𝓧 × 𝓚)} (hB_anti : Antitone B)
    (hB : ∀ n, B n ∈ supClosure (Set.image2 (· ×ˢ ·) p q)) :
    Prod.fst '' (⋂ n, B n) = ⋂ n, Prod.fst '' B n := by
  refine le_antisymm (Set.image_iInter_subset _ _) ?_
  intro x hx
  simp_rw [mem_supClosure_set_iff_natIndexedUnion] at hB
  choose S _ DC hDC hB_eq' using hB
  choose D' hD' C' hC' hDC_eq' using hDC
  let D : ℕ → ℕ → Set 𝓧 := fun n m ↦ if hm : m ∈ S n then D' n m hm else ∅
  let C : ℕ → ℕ → Set 𝓚 := fun n m ↦ if hm : m ∈ S n then C' n m hm else ∅
  have hD : ∀ n m, m ∈ S n → p (D n m) := by
    intro n m hm
    simp only [D, dite_eq_left hm]
    exact hD' n m hm
  have hC : ∀ n m, m ∈ S n → q (C n m) := by
    intro n m hm
    simp only [C, dite_eq_left hm]
    exact hC' n m hm
  have hDC_eq : ∀ n m, m ∈ S n → DC n m = D n m ×ˢ C n m := by
    intro n m hm
    simp only [D, C, dite_eq_left hm]
    exact (hDC_eq' n m hm).symm
  have hB_eq n : B n = ⋃ m ∈ S n, D n m ×ˢ C n m := by
    rw [hB_eq']
    congr with m
    by_cases hm : m ∈ S n
    · simp [hDC_eq n m hm]
    · simp [hm]
  suffices (({x} ×ˢ .univ) ∩ ⋂ n, B n).Nonempty by
    obtain ⟨u, ⟨hu_left, hu_right⟩⟩ := this
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hu_left
    rw [← hu_left, Set.mem_image]
    exact ⟨u, hu_right, rfl⟩
  let C'' n := ⋃ (m) (hm : m ∈ S n) (hx : x ∈ D n m), C n m
  have h_inter n : ({x} ×ˢ .univ) ∩ B n = {x} ×ˢ C'' n := by
    simp_rw [C'', hB_eq n, Set.inter_iUnion, Set.prod_iUnion]
    congr with m
    by_cases hm : m ∈ S n
    · by_cases hx : x ∈ D n m <;> simp <;> grind
    · simp [hm]
  have h_eq_C'' : {x} ×ˢ Set.univ ∩ ⋂ n, B n = {x} ×ˢ ⋂ n, C'' n := by
    simp_rw [Set.inter_iInter, h_inter, Set.prod_iInter]
  rw [h_eq_C'']
  suffices (⋂ n, C'' n).Nonempty by
    simpa only [Set.prod_nonempty_iff, Set.singleton_nonempty, true_and]
  have h_anti : Antitone C'' := by
    have h_eq : C'' = fun n ↦ Prod.snd '' ({x} ×ˢ .univ ∩ B n) := by
      ext n
      simp [h_inter n]
    rw [h_eq]
    intro n m hnm
    refine Set.image_mono ?_
    simp only [Set.subset_inter_iff, Set.inter_subset_left, true_and]
    exact Set.inter_subset_right.trans (hB_anti hnm)
  have hC''q n : C'' n ∈ supClosure q := by
    simp only [C'']
    rcases Finset.eq_empty_or_nonempty (S n) with hS_empty | hS_nonempty
    · simp only [hS_empty, Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
      exact subset_supClosure hq_empty
    refine finset_iUnion_mem_supClosure hS_nonempty fun m hm ↦ ?_
    by_cases hx : x ∈ D n m
    · simp only [hx, Set.iUnion_true]
      exact hC n m hm
    · simpa [hx, Set.iUnion_of_empty]
  -- `C'' n` is nonempty for all `n` since `x` is in the intersection of the `B n`,
  -- and if it were empty, then the intersection would be empty, contradiction
  have hC''_nonempty n : (C'' n).Nonempty := by
    specialize h_inter n
    by_contra! hC_empty
    simp only [hC_empty, Set.prod_empty] at h_inter
    suffices x ∈ Prod.fst '' ({x} ×ˢ Set.univ ∩ B n) by simp [h_inter] at this
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ,
      and_true, Prod.exists, exists_and_right, exists_and_left, exists_eq_right, true_and]
    simp only [Set.mem_iInter, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact hx n
  -- use that `supClosure q` is a compact system
  -- if the intersection is empty, there is a finite subintersection that is empty
  -- that subintersection is just `C'' n` for some `n` since `C''` is antitone,
  -- so `C'' n` is empty, contradiction
  have hq_compact' := IsCompactSystem.supClosure hq
  refine hq_compact'.nonempty_iInter hC''q fun n ↦ ?_
  convert hC''_nonempty n using 1
  refine le_antisymm (Set.dissipate_subset le_rfl) ?_
  simp only [Set.dissipate, Set.subset_iInter_iff]
  exact fun i hi ↦ h_anti hi

end Paving
end MeasureTheory.Analytic

end
