/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/

module

public import MeasureTheory.Analytic.Capacity.Basic
public import MeasureTheory.Analytic.Capacity.CountableClosure
public import MeasureTheory.Analytic.Paving.Projection

import all MeasureTheory.Analytic.Paving.Lemmas.FiniteUnion
/-!
# Projection of capacities and capacitable sets

## Public declarations

- `Capacity.comp_fst` equips $A\mapsto m(\operatorname{proj}_X A)$ with the
  capacity structure on
  $\operatorname{supClosure}\{A\times B:A\in p,\ B\in q\}$, assuming the
  stated closure hypotheses on $p$ and that $q$ is a compact system.
  `Capacity.comp_fst_apply` gives its evaluation formula.
- `IsCapacitable.fst` states that if $s$ is capacitable for this projected
  capacity, then $\operatorname{proj}_X(s)$ is capacitable for $m$.

The projection construction is Theorem A.5.8(ii) of Klaus Bichteler,
*Stochastic Integration with Jumps*, Cambridge University Press (2002),
Appendix A.5, ISBN 978-0-521-81129-3, and Theorem 1.35 of He, Wang, and Yan,
*Semimartingale Theory and Stochastic Calculus*, first edition, Routledge
(1992), ISBN 978-0-8493-7715-0.
-/

@[expose] public section

open Filter
open MeasureTheory
open MeasureTheory.Analytic
open scoped ENNReal NNReal Topology MeasureTheory

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓚 : Type*} {x y : 𝓧} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}


variable {m : Capacity p}

/-- The capacity obtained by composition of a capacity with a projection. -/
def Capacity.comp_fst (hp_empty : ∅ ∈ p) (hp_union : SupClosed p)
    (m : Capacity p) (hq_empty : ∅ ∈ q) (hq : IsCompactSystem q) :
    Capacity (supClosure (Set.image2 (· ×ˢ ·) p q)) where
  capacityOf s := m (Prod.fst '' s)
  mono' s t hst := m.mono (Set.image_mono hst)
  capacityOf_iUnion f hf := by
    simp only [Set.image_iUnion]
    refine capacity_iUnion ?_
    exact fun i j hij ↦ Set.image_mono (hf hij)
  capacityOf_iInter f hf hp := by
    let g n := Prod.fst '' f n
    have hg : Antitone g := fun n m hnm ↦ Set.image_mono (hf hnm)
    rw [fst_iInter_of_supClosure_image2_prod_of_antitone hq_empty hq hf hp]
    refine capacity_iInter hg fun n ↦ ?_
    simp_rw [mem_supClosure_set_iff_natIndexedUnion] at hp
    obtain ⟨S, _, u, hu_prod, hf_eq⟩ := hp n
    simp_rw [hf_eq, Set.image_iUnion]
    have hS : ∀ i ∈ S, p (Prod.fst '' u i) := by
      intro i hi
      obtain ⟨A, hA, B, hB, h_eq⟩ := hu_prod i hi
      rcases Set.eq_empty_or_nonempty B with hB | hB
      · simp only [hB, Set.prod_empty] at h_eq
        simpa [← h_eq]
      · rwa [← h_eq, Set.fst_image_prod _ hB]
    clear hf_eq
    induction S using Finset.induction with
    | empty => simpa
    | insert a s has h =>
      rw [Finset.set_biUnion_insert]
      refine hp_union ?_ ?_
      · exact hS a (Finset.mem_insert_self a s)
      · rcases Finset.eq_empty_or_nonempty s with rfl | hs
        · simpa
        refine h hs ?_ ?_
        · exact fun i hi ↦ hu_prod i (Finset.mem_insert_of_mem hi)
        · exact fun i hi ↦ hS i (Finset.mem_insert_of_mem hi)

lemma Capacity.comp_fst_apply {hp_empty : ∅ ∈ p} {hp_union : SupClosed p}
    (m : Capacity p) {hq_empty : ∅ ∈ q} {hq : IsCompactSystem q}
    (s : Set (𝓧 × 𝓚)) :
    m.comp_fst hp_empty hp_union hq_empty hq s = m (Prod.fst '' s) := rfl

/-- A set `s` is capacitable for a capacity `m` for a property `p` if `m s` can be approximated
from above by countable intersections of sets `t n` such that `p (t n)` and `⋂ n, t n ⊆ s`. -/
private lemma mem_countableInfClosure_fst {s : Set (𝓧 × 𝓚)}
    (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hq_empty : ∅ ∈ q) (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    (hs : s ∈ countableInfClosure (supClosure (Set.image2 (· ×ˢ ·) p q))) :
    (Prod.fst '' s) ∈ countableInfClosure p := by
  rw [InfClosed.mem_countableInfClosure_iff
    (InfClosed.supClosure
      (MeasureTheory.Analytic.Paving.InfClosed.image2_prod hp_inter hq_inter))]
    at hs
  obtain ⟨A, hA, hA_anti, rfl⟩ := hs
  rw [fst_iInter_of_supClosure_image2_prod_of_antitone hq_empty hq hA_anti hA]
  rw [mem_countableInfClosure_iff_iInf]
  refine ⟨fun n ↦ Prod.fst '' A n, fun n ↦ ?_, rfl⟩
  simp only
  simp_rw [mem_supClosure_set_iff_natIndexedUnion] at hA
  obtain ⟨S, _, B, hB, h_eq⟩ := hA n
  rw [h_eq]
  simp_rw [Set.image_iUnion]
  clear h_eq
  induction S using Finset.induction with
  | empty => simpa
  | insert a s has h =>
    rw [Finset.set_biUnion_insert]
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty]
      obtain ⟨u, hu, v, hv, h_eq⟩ := hB a (Finset.mem_insert_self a _)
      simp only [← h_eq]
      rcases Set.eq_empty_or_nonempty v with rfl | hv
      · simpa
      · rwa [Set.fst_image_prod _ hv]
    refine hp_union ?_ (h hs ?_)
    · obtain ⟨u, hu, v, hv, h_eq⟩ := hB a (Finset.mem_insert_self a s)
      rcases Set.eq_empty_or_nonempty v with hv | hv
      · simp only [hv, Set.prod_empty] at h_eq
        simpa [← h_eq]
      · simpa [← h_eq, Set.fst_image_prod _ hv]
    · exact fun i hi ↦ hB i (Finset.mem_insert_of_mem hi)

lemma IsCapacitable.fst (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (m : Capacity p) (hq_empty : ∅ ∈ q) (hq_inter : InfClosed q) (hq : IsCompactSystem q)
    {s : Set (𝓧 × 𝓚)} (hs : IsCapacitable (m.comp_fst hp_empty hp_union hq_empty hq) s) :
    IsCapacitable m (Prod.fst '' s) := by
  intro a ha
  choose t ht_mono ht_subset ht_le using hs a ha
  exact ⟨Prod.fst '' t,
    mem_countableInfClosure_fst hp_empty hp_inter hp_union hq_empty hq_inter hq ht_mono,
    Set.image_mono ht_subset, ht_le⟩

end MeasureTheory.Analytic.Paving

end
