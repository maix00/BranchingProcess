/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/
module

public import MeasureTheory.Analytic.Paving.Analytic.Basic
import Mathlib.Basic.Real.Basic
import Topology.Compactness.CompactSystem.Operations

/-!
# Set operations on paving-analytic sets

This module proves closure of paving-analytic sets under countable and finite set operations and
under the generated countable paving closures.

## Public declarations

- `IsPavingAnalyticFor.exists_mem_countableSupClosure_superset` gives
  $IsPavingAnalyticFor(p,K,s)\Rightarrow
  \exists t\in countableSupClosure(p),\ s\subseteq t$.
- `IsPavingAnalyticFor.empty` and `IsPavingAnalytic.empty` construct analytic representations of
  $\varnothing$ when $\varnothing\in p$; `isPavingAnalyticFor_iff_eq_empty` characterizes the
  empty-witness-space case by $s=\varnothing$.
- `IsPavingAnalyticFor.iInter` and `IsPavingAnalytic.iInter` preserve
  $s=\bigcap_n s_n$ under analytic hypotheses; the For version uses witness $\prod_n K_n$.
  `IsPavingAnalyticFor.iUnion` and `IsPavingAnalytic.iUnion` preserve
  $s=\bigcup_n s_n$; the For version uses witness $\sum_n K_n$.
- `IsPavingAnalyticFor.inter` and `IsPavingAnalytic.inter` preserve
  $s\cap t$; `IsPavingAnalyticFor.union` and `IsPavingAnalytic.union` preserve $s\cup t$.
- `isPavingAnalyticFor_of_mem_countableInfClosure_of_imp` and
  `isPavingAnalytic_of_mem_countableInfClosure_of_imp` transfer
  $s\in countableInfClosure(p')$ to paving-analyticity when every member of p' is analytic.
  `isPavingAnalyticFor_of_mem_countableSupClosure_of_imp` and
  `isPavingAnalytic_of_mem_countableSupClosure_of_imp` give the corresponding result for
  $countableSupClosure(p')$.
- `IsPavingAnalyticFor.inter_set` constructs an analytic witness for $s\cap t$ under the paving
  $\{u\mid\exists v\in p,\ u=v\cap t\}$; `exists_isPavingAnalyticFor_of_inter_set` recovers
  $s'$ with $s=s'\cap t$.

## References

He, Wang, and Yan, Semimartingale Theory and Stochastic Calculus, first edition, Routledge
(1992), Theorems 1.25–1.31, ISBN 978-0-8493-7715-0.
-/
@[expose] public section

open scoped MeasureTheory
open MeasureTheory

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}

-- Construction following He, Wang, and Yan, Theorem 1.25.
lemma IsPavingAnalyticFor.exists_mem_countableSupClosure_superset (hs : IsPavingAnalyticFor p 𝓚 s) :
    ∃ t, t ∈ countableSupClosure p ∧ s ⊆ t := by
  obtain ⟨q, hq_empty, hq_compact, B, hB_prod, rfl⟩ := hs
  rw [mem_prodSigmaDelta_iff] at hB_prod
  obtain ⟨A, hA, K, hK, rfl⟩ := hB_prod
  simp_rw [mem_countableSupClosure_iff_iSup]
  refine ⟨⋃ m, A 0 m, ?_, ?_⟩
  · exact ⟨fun m ↦ A 0 m, hA 0, rfl⟩
  · intro x hx
    simp only [Set.mem_image, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Prod.exists,
      exists_and_right, exists_eq_right] at hx ⊢
    obtain ⟨_, h⟩ := hx
    choose n hn _ using h
    exact ⟨n 0, hn 0⟩

lemma IsPavingAnalyticFor.empty (𝓚 : Type*) (hp_empty : ∅ ∈ p) : IsPavingAnalyticFor p 𝓚 ∅ := by
  rcases isEmpty_or_nonempty 𝓚 with h_empty | h_nonempty
  · refine ⟨Set.univ, by simp, ?_, ∅ ×ˢ ∅, mem_prodSigmaDelta_of_mem hp_empty (by simp), by simp⟩
    simp only [IsCompactSystem]
    intro C _ _
    have h_eq_empty n : C n = ∅ := Set.eq_empty_of_isEmpty (C n)
    refine ⟨0, ?_⟩
    simpa using h_eq_empty 0
  · exact isPavingAnalyticFor_of_mem 𝓚 hp_empty

@[simp]
lemma IsPavingAnalytic.empty (hp_empty : ∅ ∈ p) : IsPavingAnalytic p ∅ :=
  (IsPavingAnalyticFor.empty ℝ hp_empty).isPavingAnalytic

@[simp]
lemma isPavingAnalyticFor_iff_eq_empty (𝓚 : Type*) [IsEmpty 𝓚] (hp_empty : ∅ ∈ p) (s : Set 𝓧) :
    IsPavingAnalyticFor p 𝓚 s ↔ s = ∅ := by
  refine ⟨fun hs ↦ ?_, fun hs_empty ↦ ?_⟩
  · obtain ⟨q, hq_empty, hq_compact, t, h_prod, h_eq⟩ := hs
    rw [h_eq]
    simp only [Set.image_eq_empty]
    exact Set.eq_empty_of_isEmpty t
  · rw [hs_empty]
    exact IsPavingAnalyticFor.empty 𝓚 hp_empty

-- He, Wang, and Yan, Theorem 1.26.
lemma IsPavingAnalyticFor.iInter {𝓚 : ℕ → Type*} {s : ℕ → Set 𝓧}
    (hs : ∀ n, IsPavingAnalyticFor p (𝓚 n) (s n)) :
    IsPavingAnalyticFor p (Π n, 𝓚 n) (⋂ n, s n) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  let C n : Set (𝓧 × ((i : ℕ) → 𝓚 i)) := {p | (p.1, p.2 n) ∈ B n}
  let q' : Set (Set (Π n, 𝓚 n)) :=
    -- modeled on squareCylinders, but with univ instead of a finset
    Set.univ.pi '' (Set.univ.pi (fun n ↦ insert Set.univ (q n)))
  refine ⟨q', ?_, ?_, ⋂ n, C n, ?_, ?_⟩
  · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, Set.univ_pi_eq_empty_iff, q']
    exact ⟨fun _ ↦ ∅, by simp only [exists_const, and_true]; exact fun _ ↦ .inr (hq_empty _)⟩
  · exact IsCompactSystem.pi hq_compact
  · refine countableInfClosed_countableInfClosure.iInf_mem fun n ↦ ?_
    rw [← prodSigmaDelta]
    simp_rw [mem_prodSigmaDelta_iff] at hB_prod ⊢
    choose A hA K hK hB_eq using hB_prod
    refine ⟨A n, hA n, fun i j ↦ {y | y n ∈ K n i j}, fun i j ↦ ?_, ?_⟩
    · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, q']
      rcases Set.eq_empty_or_nonempty (K n i j) with hK_empty | hK_nonempty
      · simp only [hK_empty, Set.mem_empty_iff_false, Set.ofPred_false]
        exact ⟨fun _ ↦ ∅, by
          simp only [Set.univ_pi_empty, and_true]; exact fun _ ↦ .inr (hq_empty _)⟩
      refine ⟨fun k ↦ if k = n then K k i j else Set.univ, fun k ↦ ?_, ?_⟩
      · simp only
        split_ifs with hk
        · subst hk
          exact .inr (hK k i j)
        · simp
      · ext; simp
    ext
    simp [hB_eq, C]
  · simp_rw [hB_eq]
    ext x
    simp only [Set.mem_iInter, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Set.mem_ofPred_eq, C]
    refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ n ↦ ⟨y n, hy n⟩⟩
    choose y hy using h
    exact ⟨y, hy⟩

lemma IsPavingAnalytic.iInter {s : ℕ → Set 𝓧} (hs : ∀ n, IsPavingAnalytic p (s n)) :
    IsPavingAnalytic p (⋂ n, s n) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.iInter hs𝓚).isPavingAnalytic

-- He, Wang, and Yan, Theorem 1.26.
lemma IsPavingAnalyticFor.iUnion {𝓚 : ℕ → Type*} {s : ℕ → Set 𝓧}
    (hs : ∀ n, IsPavingAnalyticFor p (𝓚 n) (s n)) :
    IsPavingAnalyticFor p (Σ n, 𝓚 n) (⋃ n, s n) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  let C := Prod.swap ''
    ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' (Set.sigma Set.univ (fun n ↦ Prod.swap '' (B n))))
  let q'' := {t : Set (Σ n, 𝓚 n) |
    ∃ s : Finset ℕ, t ∈ (s : Set ℕ).sigma '' (Set.univ.pi (fun n ↦ insert Set.univ (q n)))}
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const, q'']
    exact ⟨∅, fun _ ↦ Set.univ, by simp⟩
  · exact IsCompactSystem.sigma (fun n ↦ (hq_compact n).insert_univ)
  · unfold prodSigmaDelta at hB_prod
    simp_rw [mem_countableInfClosure_iff_iInf] at hB_prod
    choose A hA hB_eq using hB_prod
    have hC_eq : C = ⋂ k, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm ''
        (Set.sigma Set.univ (fun n ↦ Prod.swap '' (A n k)))) := by
      simp only [C, ← hB_eq]
      rw [← Set.image_iInter Prod.swap_bijective, ← Set.image_iInter (Equiv.bijective _)]
      simp only [Equiv.sigmaProdDistrib_symm_apply, Set.iInf_eq_iInter]
      simp_rw [Set.image_iInter Prod.swap_bijective]
      congr
      ext
      simp
    rw [hC_eq]
    refine countableInfClosed_countableInfClosure.iInf_mem fun k ↦ subset_countableInfClosure ?_
    simp_rw [mem_countableSupClosure_image2_prod_iff] at hA
    choose B hB K hK hA_eq using hA
    simp_rw [hA_eq]
    have h_eq : Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' ⋃ n_1, B n k n_1 ×ˢ K n k n_1)
      = ⋃ n_1, Prod.swap '' ((Equiv.sigmaProdDistrib 𝓚 𝓧).symm '' Set.univ.sigma
        fun n ↦ Prod.swap '' (B n k n_1 ×ˢ K n k n_1)) := by ext; simp; grind
    rw [h_eq]
    refine countableSupClosed_countableSupClosure.iSup_mem fun i ↦ ?_
    simp only [Set.image_swap_prod, Set.sigma_eq_biUnion, Set.mem_univ, Set.iUnion_true,
      Set.image_iUnion]
    refine countableSupClosed_countableSupClosure.iSup_mem fun j ↦ subset_countableSupClosure ?_
    refine ⟨B j k i, hB _ _ _, Sigma.mk j '' (K j k i), ?_, by ext; simp; grind⟩
    simp only [Set.mem_image, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const, q'']
    refine ⟨{j}, fun j ↦ K j k i, ?_⟩
    simp only [Finset.coe_singleton, Set.singleton_sigma, and_true]
    exact fun m ↦ .inr (hK _ _ _)
  · simp only [hB_eq, Equiv.sigmaProdDistrib_symm_apply, C]
    ext y
    simp only [Set.mem_iUnion, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      Set.mem_sigma_iff, Set.mem_univ, Prod.swap_prod_mk, true_and, Sigma.exists, Prod.mk.injEq,
      ↓existsAndEq, exists_eq_right_right, Sigma.mk.injEq, and_true]
    grind

lemma IsPavingAnalytic.iUnion {s : ℕ → Set 𝓧} (hs : ∀ n, IsPavingAnalytic p (s n)) :
    IsPavingAnalytic p (⋃ n, s n) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.iUnion hs𝓚).isPavingAnalytic

-- He, Wang, and Yan, Theorem 1.26.
lemma IsPavingAnalyticFor.inter {𝓚' : Type*} {t : Set 𝓧}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : IsPavingAnalyticFor p 𝓚' t) :
    IsPavingAnalyticFor p (𝓚 × 𝓚') (s ∩ t) := by
  obtain ⟨q, hq_empty, hq_compact, B, hB_prod, hB_eq⟩ := hs
  obtain ⟨q', hq'_empty, hq'_compact, B', hB'_prod, hB'_eq⟩ := ht
  let C : Set (𝓧 × (𝓚 × 𝓚')) := {p | (p.1, p.2.1) ∈ B}
  let C' : Set (𝓧 × (𝓚 × 𝓚')) := {p | (p.1, p.2.2) ∈ B'}
  let q'' : Set (Set (𝓚 × 𝓚')) := Set.image2 (· ×ˢ ·) (insert Set.univ q) (insert Set.univ q')
  refine ⟨q'', ?_, ?_, C ∩ C', ?_, ?_⟩
  · simp [q'']
    grind
  · exact IsCompactSystem.image2_prod hq_compact.insert_univ hq'_compact.insert_univ
  · refine infClosed_countableInfClosure ?_ ?_
    · rw [← prodSigmaDelta]
      simp_rw [mem_prodSigmaDelta_iff] at hB_prod ⊢
      choose A hA K hK hB_eq using hB_prod
      refine ⟨A, hA, fun i j ↦ {y | y.1 ∈ K i j}, fun i j ↦ ?_, ?_⟩
      · simp only [q'']
        rcases Set.eq_empty_or_nonempty (K i j) with hK_empty | hK_nonempty
        · simp only [hK_empty, Set.mem_empty_iff_false, Set.ofPred_false]
          exact ⟨∅, by simp [hq_empty]⟩
        refine ⟨K i j, ?_⟩
        simp only [Set.mem_insert_iff, hK, or_true, exists_eq_or_imp, true_and]
        left
        ext
        simp
      · ext y
        simp only [hB_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq, C]
    · rw [← prodSigmaDelta]
      simp_rw [mem_prodSigmaDelta_iff] at hB'_prod ⊢
      choose A hA K hK hB_eq using hB'_prod
      refine ⟨A, hA, fun i j ↦ {y | y.2 ∈ K i j}, fun i j ↦ ?_, ?_⟩
      · simp only [q'']
        rcases Set.eq_empty_or_nonempty (K i j) with hK_empty | hK_nonempty
        · simp only [hK_empty, Set.mem_empty_iff_false, Set.ofPred_false]
          exact ⟨∅, by simp [hq_empty]⟩
        simp only [Set.mem_image2, Set.mem_insert_iff, exists_eq_or_imp, Set.univ_prod_univ]
        left
        right
        refine ⟨K i j, ?_⟩
        simp only [hK, true_and]
        ext
        simp
      · ext y
        simp only [hB_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq, C']
  · ext
    simp [hB_eq, hB'_eq, C, C']

lemma IsPavingAnalytic.inter {t : Set 𝓧}
    (hs : IsPavingAnalytic p s) (ht : IsPavingAnalytic p t) :
    IsPavingAnalytic p (s ∩ t) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  choose 𝓚' h𝓚' ht𝓚' using ht
  exact (IsPavingAnalyticFor.inter hs𝓚 ht𝓚').isPavingAnalytic

-- He, Wang, and Yan, Theorem 1.26.
lemma IsPavingAnalyticFor.union.{u} {𝓚 𝓚' : Type u} {t : Set 𝓧}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : IsPavingAnalyticFor p 𝓚' t) :
    IsPavingAnalyticFor p (𝓚 ⊕ 𝓚') (s ∪ t) := by
  choose q hq_empty hq_compact B hB_prod hB_eq using hs
  choose q' hq'_empty hq'_compact B' hB'_prod hB'_eq using ht
  let C : Set (𝓧 × (𝓚 ⊕ 𝓚')) :=
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (B, B')
  let q'' := {t | Sum.inl ⁻¹' t ∈ insert Set.univ q ∧ Sum.inr ⁻¹' t ∈ insert Set.univ q'}
  refine ⟨q'', ?_, ?_, C, ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_ofPred_eq,
      Set.subset_empty_iff, Set.range_eq_empty_iff, Set.preimage_empty, q'']
    exact ⟨.inr hq_empty, .inr hq'_empty⟩
  · exact IsCompactSystem.sum hq_compact.insert_univ hq'_compact.insert_univ
  · unfold prodSigmaDelta at hB_prod hB'_prod
    simp_rw [mem_countableInfClosure_iff_iInf] at hB_prod hB'_prod
    choose A hA hB_eq using hB_prod
    choose A' hA' hB'_eq using hB'_prod
    have hC_eq : C = ⋂ k,
    (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm (A k, A' k) := by
      simp only [C, ← hB_eq, ← hB'_eq]
      rw [← Set.image_iInter (Equiv.bijective _)]
      congr
      calc Set.sumEquiv.symm (⋂ n, A n, ⋂ n, A' n)
      _ = Set.sumEquiv.symm (⨅ n, (A n, A' n)) := by
        congr 1
        ext <;> simp [iInf, Prod.fst_sInf, Prod.snd_sInf]
      _ = ⨅ n, Set.sumEquiv.symm (A n, A' n) := OrderIso.map_iInf _ _
      _ = ⋂ i, Set.sumEquiv.symm (A i, A' i) := rfl
    rw [hC_eq]
    refine countableInfClosed_countableInfClosure.iInf_mem fun k ↦ subset_countableInfClosure ?_
    simp_rw [mem_countableSupClosure_image2_prod_iff] at hA hA'
    choose B hB K hK hA_eq using hA
    choose B' hB' K' hK' hA'_eq using hA'
    simp_rw [hA_eq, hA'_eq]
    have h_eq : (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (⋃ n, B k n ×ˢ K k n, ⋃ n, B' k n ×ˢ K' k n)
        = ⋃ n, (Equiv.prodSumDistrib 𝓧 𝓚 𝓚').symm '' Set.sumEquiv.symm
          (B k n ×ˢ K k n, B' k n ×ˢ K' k n) := by
      rw [← Set.image_iUnion]
      congr 1
      calc Set.sumEquiv.symm (⋃ n, B k n ×ˢ K k n, ⋃ n, B' k n ×ˢ K' k n)
      _ = Set.sumEquiv.symm (⨆ n, (B k n ×ˢ K k n, B' k n ×ˢ K' k n)) := by
        congr 1
        ext <;> simp [iSup, Prod.fst_sSup, Prod.snd_sSup]
      _ = ⨆ n, Set.sumEquiv.symm (B k n ×ˢ K k n, B' k n ×ˢ K' k n) := OrderIso.map_iSup _ _
      _ = ⋃ i, Set.sumEquiv.symm (B k i ×ˢ K k i, B' k i ×ˢ K' k i) := rfl
    rw [h_eq]
    refine countableSupClosed_countableSupClosure.iSup_mem fun i ↦ ?_
    simp only [Set.sumEquiv, OrderIso.symm_mk, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw [Set.image_union]
    refine supClosed_countableSupClosure
      (subset_countableSupClosure ?_) (subset_countableSupClosure ?_)
    · refine ⟨B k i, hB _ _, Sum.inl '' (K k i), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_ofPred_eq,
          Set.preimage_inr_image_inl, q'']
        refine ⟨.inr ?_, .inr hq'_empty⟩
        convert hK k i
        ext
        simp
      · ext; simp [Equiv.prodSumDistrib]; grind
    · refine ⟨B' k i, hB' _ _, Sum.inr '' (K' k i), ?_, ?_⟩
      · simp only [Set.mem_insert_iff, Set.preimage_eq_univ_iff, Set.mem_ofPred_eq,
          Set.preimage_inl_image_inr, q'']
        refine ⟨.inr hq_empty, .inr ?_⟩
        convert hK' k i
        ext
        simp
      · ext; simp [Equiv.prodSumDistrib]; grind
  · simp only [hB_eq, hB'_eq, C]
    ext
    simp [Equiv.prodSumDistrib, Equiv.sumProdDistrib, Set.sumEquiv]

lemma IsPavingAnalytic.union {t : Set 𝓧}
    (hs : IsPavingAnalytic p s) (ht : IsPavingAnalytic p t) :
    IsPavingAnalytic p (s ∪ t) := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  choose 𝓚' h𝓚' ht𝓚' using ht
  exact (IsPavingAnalyticFor.union hs𝓚 ht𝓚').isPavingAnalytic

lemma isPavingAnalyticFor_of_mem_countableInfClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableInfClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalyticFor p 𝓚 x) :
    IsPavingAnalyticFor p (Π _ : ℕ, 𝓚) s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalyticFor.iInter fun n ↦ hqp _ (hA n)

lemma isPavingAnalytic_of_mem_countableInfClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableInfClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalytic p x) :
    IsPavingAnalytic p s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalytic.iInter fun n ↦ hqp _ (hA n)

lemma isPavingAnalyticFor_of_mem_countableSupClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableSupClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalyticFor p 𝓚 x) :
    IsPavingAnalyticFor p (Σ _ : ℕ, 𝓚) s := by
  rw [mem_countableSupClosure_iff_iSup] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalyticFor.iUnion fun n ↦ hqp _ (hA n)

lemma isPavingAnalytic_of_mem_countableSupClosure_of_imp {p' : Set (Set 𝓧)}
    (hs : s ∈ countableSupClosure p') (hqp : ∀ x, x ∈ p' → IsPavingAnalytic p x) :
    IsPavingAnalytic p s := by
  rw [mem_countableSupClosure_iff_iSup] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact IsPavingAnalytic.iUnion fun n ↦ hqp _ (hA n)

-- He, Wang, and Yan, Theorem 1.28.
/-- The projection of an analytic set is analytic. -/

lemma IsPavingAnalyticFor.inter_set (hs : IsPavingAnalyticFor p 𝓚 s) (t : Set 𝓧) :
    IsPavingAnalyticFor {u | ∃ v, v ∈ p ∧ u = v ∩ t} 𝓚 (s ∩ t) := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  let A' := (t ×ˢ .univ) ∩ A
  refine ⟨q, hq_empty, hq, A', ?_, by ext; simp; grind⟩
  simp_rw [mem_prodSigmaDelta_iff] at hA ⊢
  obtain ⟨B, hB, K, hK, rfl⟩ := hA
  refine ⟨fun n m ↦ B n m ∩ t, fun n m ↦ ⟨B n m, hB n m, rfl⟩, K, hK, ?_⟩
  simp only [A']
  simp_rw [Set.inter_iInter, Set.inter_iUnion]
  congr with
  simp
  grind

-- He, Wang, and Yan, Theorem 1.30.
lemma exists_isPavingAnalyticFor_of_inter_set (t : Set 𝓧)
    (hs : IsPavingAnalyticFor {u | ∃ v, v ∈ p ∧ u = v ∩ t} 𝓚 s) :
    ∃ s', IsPavingAnalyticFor p 𝓚 s' ∧ s = s' ∩ t := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  rw [mem_prodSigmaDelta_iff] at hA
  obtain ⟨B, hB, K, hK, rfl⟩ := hA
  choose A' hA' hBA' using hB
  refine ⟨Prod.fst '' (⋂ n, ⋃ m, A' n m ×ˢ K n m), ?_, ?_⟩
  · refine ⟨q, hq_empty, hq, ?_⟩
    refine ⟨⋂ n, ⋃ m, A' n m ×ˢ K n m, ?_, rfl⟩
    rw [mem_prodSigmaDelta_iff]
    exact ⟨A', hA', K, hK, rfl⟩
  · simp only [hBA']
    have h_eq n m : (A' n m ∩ t) ×ˢ K n m = (A' n m ×ˢ K n m) ∩ (t ×ˢ .univ) := by
      ext; simp; grind
    simp_rw [h_eq, ← Set.iUnion_inter, ← Set.iInter_inter]
    suffices h_eq' : ∀ (s : Set (𝓧 × 𝓚)), Prod.fst '' (s ∩ (t ×ˢ .univ)) = Prod.fst '' s ∩ t by
      rw [h_eq']
    intro s
    ext s
    simp

-- He, Wang, and Yan, Theorem 1.31.
end MeasureTheory.Analytic.Paving

end
