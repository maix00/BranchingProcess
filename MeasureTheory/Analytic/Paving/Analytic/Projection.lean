/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/
module

public import MeasureTheory.Analytic.Paving.Analytic.Operations
import Topology.Compactness.CompactSystem.Operations

/-!
# Products and projections of paving-analytic sets

This module proves that paving-analyticity is preserved by products, products with paving members,
and coordinate projections, including products formed from countable paving closures.

## Public declarations

- `IsPavingAnalyticFor.fst` states that if s is analytic for the product paving $p\times q$ and
  q is a compact system containing $\varnothing$, then $Prod.fst''s$ is analytic for p.
  `IsPavingAnalytic.fst` is the corresponding result without a fixed witness type.
- `IsPavingAnalyticFor.prod_left` and `IsPavingAnalytic.prod_left` show that if $t\in r$ and s is
  analytic for p, then $t\times s$ is analytic for the product paving $r\times p$.
  `IsPavingAnalyticFor.prod_right` and `IsPavingAnalytic.prod_right` state the symmetric product.
- `isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_left`,
  `isPavingAnalytic_of_image2_prod_isPavingAnalytic_left`,
  `isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right`, and
  `isPavingAnalytic_of_image2_prod_isPavingAnalytic_right` lift analytic factors through
  $Set.image2((\cdot\timesˢ\cdot),r,p)$.
- `isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_left` and
  `isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_right` handle
  countable sup-closures of these product pavings.
- `IsPavingAnalyticFor.prod_mem_countableSupClosure_left` and
  `IsPavingAnalyticFor.prod_mem_countableSupClosure_right` place products with members of
  $countableSupClosure(r)$ in a countable sup-closure of the product paving.
- `IsPavingAnalyticFor.prod` and `IsPavingAnalytic.prod` preserve $s\times t$.
- `isPavingAnalyticFor_isPavingAnalyticFor` and `isPavingAnalytic_isPavingAnalytic` flatten
  iterated analytic witnesses; `isPavingAnalytic_isPavingAnalytic_iff` gives the equivalence
  $IsPavingAnalytic(IsPavingAnalytic(p),s)\leftrightarrow IsPavingAnalytic(p,s)$.

## References

He, Wang, and Yan, Semimartingale Theory and Stochastic Calculus, first edition, Routledge
(1992), Theorems 1.32–1.33, ISBN 978-0-8493-7715-0.
-/
@[expose] public section

open scoped MeasureTheory
open MeasureTheory

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}

lemma IsPavingAnalyticFor.fst {𝓚' : Type*} (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p q) 𝓚' s) :
    IsPavingAnalyticFor p (𝓚 × 𝓚') (Prod.fst '' s) := by
  obtain ⟨q', hq'_empty, hq', K, hK, rfl⟩ := hs
  refine ⟨Set.image2 (· ×ˢ ·) q q', ?_,
    IsCompactSystem.image2_prod hq hq',
    Equiv.prodAssoc 𝓧 𝓚 𝓚' '' K, ?_,
    by ext; simp⟩
  · exact ⟨∅, hq_empty, ∅, hq'_empty, by simp⟩
  simp_rw [mem_prodSigmaDelta_iff] at hK ⊢
  obtain ⟨B, hB, K', hK', rfl⟩ := hK
  choose A hA K hK h_eq using hB
  refine ⟨A, hA, fun n m ↦ K n m ×ˢ K' n m, fun n m ↦ ?_, ?_⟩
  · exact ⟨K n m, hK n m, K' n m, hK' n m, rfl⟩
  · rw [Set.image_iInter (Equiv.prodAssoc 𝓧 𝓚 𝓚').bijective]
    simp_rw [Set.image_iUnion]
    congr
    ext
    simp
    grind

/-- The projection of an analytic set is analytic. -/
lemma IsPavingAnalytic.fst {𝓚 : Type} [Nonempty 𝓚] {q : Set (Set 𝓚)}
    (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsPavingAnalytic (Set.image2 (· ×ˢ ·) p q) s) :
    IsPavingAnalytic p (Prod.fst '' s) := by
  obtain ⟨𝓚', h𝓚', hs𝓚'⟩ := hs
  exact (hs𝓚'.fst hq_empty hq).isPavingAnalytic

lemma IsPavingAnalyticFor.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) 𝓚 (t ×ˢ s) := by
  obtain ⟨q, hq_empty, hq_compact, s', hs_prod, hs_eq⟩ := hs
  have h_eq' : t ×ˢ s = Prod.fst '' ((Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s')) := by
    ext; simp; grind
  refine ⟨q, hq_empty, hq_compact, (Equiv.prodAssoc _ _ _).symm '' (t ×ˢ s'), ?_, h_eq'⟩
  simp_rw [mem_prodSigmaDelta_iff] at hs_prod ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs_prod
  refine ⟨fun n m ↦ t ×ˢ A n m, fun n m ↦ ?_, K, hK, ?_⟩
  · exact ⟨t, ht, A n m, hA n m, rfl⟩
  · rw [Set.prod_iInter, Set.image_iInter (Equiv.prodAssoc _ _ _).symm.bijective]
    congr with
    simp
    grind

lemma IsPavingAnalytic.prod_left {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (ht : r t) (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) (t ×ˢ s) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_left ht).isPavingAnalytic

lemma IsPavingAnalyticFor.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalyticFor p 𝓚 s) (ht : r t) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) 𝓚 (s ×ˢ t) := by
  obtain ⟨q, hq_empty, hq_compact, s', hs_prod, hs_eq⟩ := hs
  have h_eq' : s ×ˢ t = Prod.fst '' ((Equiv.prodAssoc _ _ _).symm ''
      (Prod.map id Prod.swap '' ((Equiv.prodAssoc _ _ _) '' (s' ×ˢ t)))) := by
    congr with
    simp
    grind
  refine ⟨q, hq_empty, hq_compact, (Equiv.prodAssoc _ _ _).symm ''
      (Prod.map id Prod.swap '' ((Equiv.prodAssoc _ _ _) '' (s' ×ˢ t))), ?_, h_eq'⟩
  simp_rw [mem_prodSigmaDelta_iff] at hs_prod ⊢
  obtain ⟨A, hA, K, hK, rfl⟩ := hs_prod
  refine ⟨fun n m ↦ A n m ×ˢ t, fun n m ↦ ?_, K, hK, ?_⟩
  · exact ⟨A n m, hA n m, t, ht, rfl⟩
  · have hprod {B : ℕ → Set (𝓧 × 𝓚)} :
        (⋂ n, B n) ×ˢ t = ⋂ n, B n ×ˢ t := by
      ext x
      simp only [Set.mem_prod, Set.mem_iInter]
      constructor
      · rintro ⟨hx, ht⟩ n
        exact ⟨hx n, ht⟩
      · intro hx
        refine ⟨fun n ↦ (hx n).1, ?_⟩
        exact (hx 0).2
    rw [hprod, Set.image_iInter (Equiv.prodAssoc _ _ _).bijective,
      Set.image_iInter, Set.image_iInter (Equiv.prodAssoc _ _ _).symm.bijective]
    swap; · exact Function.bijective_id.prodMap Prod.swap_bijective
    congr with n x
    simp
    grind

lemma IsPavingAnalytic.prod_right {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set 𝓨}
    (hs : IsPavingAnalytic p s) (ht : r t) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) p r) (s ×ˢ t) := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact (hs𝓚.prod_right ht).isPavingAnalytic

lemma isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : t ∈ Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚)) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) 𝓚 t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalytic_of_image2_prod_isPavingAnalytic_left {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓨 × 𝓧)} (ht : t ∈ Set.image2 (· ×ˢ ·) r (IsPavingAnalytic p)) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hs.prod_left hA

lemma isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : t ∈ Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) 𝓚 t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalytic_of_image2_prod_isPavingAnalytic_right {𝓨 : Type*} {r : Set 𝓨 → Prop}
    {t : Set (𝓧 × 𝓨)} (ht : t ∈ Set.image2 (· ×ˢ ·) (IsPavingAnalytic p) r) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) p r) t := by
  obtain ⟨A, hA, s, hs, rfl⟩ := ht
  exact hA.prod_right hs

lemma isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_left
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓨 × 𝓧)}
    (ht : t ∈ countableSupClosure (Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚))) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp
    (p' := Set.image2 (· ×ˢ ·) r (IsPavingAnalyticFor p 𝓚)) ht fun s hs ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_left hs

lemma isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_right
    {𝓨 : Type*} {r : Set 𝓨 → Prop} {t : Set (𝓧 × 𝓨)}
    (ht : t ∈ countableSupClosure (Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r)) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) (Σ _ : ℕ, 𝓚) t := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp
    (p' := Set.image2 (· ×ˢ ·) (IsPavingAnalyticFor p 𝓚) r) ht fun s hs ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right hs

lemma IsPavingAnalyticFor.prod_mem_countableSupClosure_left {𝓨 : Type*} {r : Set (Set 𝓨)}
    {t : Set 𝓨} (ht : t ∈ countableSupClosure r) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) (Σ _ : ℕ, 𝓚) (t ×ˢ s) := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_left ?_
  rw [mem_countableSupClosure_iff_iSup] at ht ⊢
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ A n ×ˢ s, fun n ↦ ⟨A n, hA n, s, hs, rfl⟩, ?_⟩
  simp only [Set.iSup_eq_iUnion]
  rw [Set.iUnion_prod_const]

lemma IsPavingAnalyticFor.prod_mem_countableSupClosure_right {𝓨 : Type*} {r : Set (Set 𝓨)}
    {t : Set 𝓨} (hs : IsPavingAnalyticFor p 𝓚 s) (ht : t ∈ countableSupClosure r) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p r) (Σ _ : ℕ, 𝓚) (s ×ˢ t) := by
  refine isPavingAnalyticFor_of_mem_countableSupClosure_image2_prod_isPavingAnalyticFor_right ?_
  rw [mem_countableSupClosure_iff_iSup] at ht ⊢
  obtain ⟨A, hA, rfl⟩ := ht
  refine ⟨fun n ↦ s ×ˢ A n, fun n ↦ ⟨s, hs, A n, hA n, rfl⟩, ?_⟩
  simp only [Set.iSup_eq_iUnion]
  rw [Set.prod_iUnion]

-- He, Wang, and Yan, Theorem 1.27.
lemma IsPavingAnalyticFor.prod {𝓨 𝓚' : Type*} {r : Set (Set 𝓨)} {t : Set 𝓨}
    (ht : IsPavingAnalyticFor r 𝓚' t) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) r p) ((Σ _ : ℕ, 𝓚') × (Σ _ : ℕ, 𝓚)) (t ×ˢ s) := by
  obtain ⟨t₁, ht₁, ht₁_subset⟩ := ht.exists_mem_countableSupClosure_superset
  obtain ⟨s₁, hs₁, hs₁_subset⟩ := hs.exists_mem_countableSupClosure_superset
  have h_eq : t ×ˢ s = (t ×ˢ s₁) ∩ (t₁ ×ˢ s) := by ext; simp; grind
  rw [h_eq]
  refine IsPavingAnalyticFor.inter ?_ ?_
  · exact ht.prod_mem_countableSupClosure_right hs₁
  · exact hs.prod_mem_countableSupClosure_left ht₁

lemma IsPavingAnalytic.prod {𝓨 : Type*} {r : Set (Set 𝓨)} {t : Set 𝓨}
    (ht : IsPavingAnalytic r t) (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) r p) (t ×ˢ s) := by
  obtain ⟨𝓚', h𝓚', ht'⟩ := ht
  obtain ⟨𝓚, h𝓚, hs'⟩ := hs
  exact (IsPavingAnalyticFor.prod ht' hs').isPavingAnalytic

-- He, Wang, and Yan, Theorem 1.29.
lemma isPavingAnalyticFor_isPavingAnalyticFor
    (hs : IsPavingAnalyticFor (IsPavingAnalyticFor p 𝓚) 𝓚 s) :
    IsPavingAnalyticFor p (𝓚 × (ℕ → (_ : ℕ) × 𝓚)) s := by
  obtain ⟨q, hq_empty, hq, t, ht, rfl⟩ := hs
  suffices IsPavingAnalyticFor (Set.image2 (· ×ˢ ·) p q) (ℕ → (_ : ℕ) × 𝓚) t by
    exact this.fst hq_empty hq
  refine isPavingAnalyticFor_of_mem_countableInfClosure_of_imp ht fun t ht ↦ ?_
  refine isPavingAnalyticFor_of_mem_countableSupClosure_of_imp ht fun t ht ↦ ?_
  exact isPavingAnalyticFor_of_image2_prod_isPavingAnalyticFor_right ht

lemma isPavingAnalytic_isPavingAnalytic (hs : IsPavingAnalytic (IsPavingAnalytic p) s) :
    IsPavingAnalytic p s := by
  obtain ⟨𝓚, h𝓚, hs'⟩ := hs
  obtain ⟨q, hq_empty, hq, t, ht, rfl⟩ := hs'
  suffices IsPavingAnalytic (Set.image2 (· ×ˢ ·) p q) t from (this.fst hq_empty hq)
  refine isPavingAnalytic_of_mem_countableInfClosure_of_imp ht fun t ht ↦ ?_
  refine isPavingAnalytic_of_mem_countableSupClosure_of_imp ht fun t ht ↦ ?_
  exact isPavingAnalytic_of_image2_prod_isPavingAnalytic_right ht

@[simp]
lemma isPavingAnalytic_isPavingAnalytic_iff :
    IsPavingAnalytic (IsPavingAnalytic p) s ↔ IsPavingAnalytic p s :=
  ⟨isPavingAnalytic_isPavingAnalytic, fun hs ↦ isPavingAnalytic_of_mem hs⟩

-- He, Wang, and Yan, Theorem 1.30.
end MeasureTheory.Analytic.Paving

end
