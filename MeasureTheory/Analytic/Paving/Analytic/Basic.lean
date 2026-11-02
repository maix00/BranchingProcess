/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/
module

public import MeasureTheory.Analytic.Paving.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Basic.Real.Basic
import Topology.Compactness.CompactSystem.Operations

/-!
# Paving-analytic sets: definitions and basic properties

This module defines analytic sets for a paving and proves their basic measurability and
monotonicity properties.

## Public declarations

- `IsPavingAnalyticFor` p K s means
  $\exists q,t,\ \varnothing\in q\land IsCompactSystem(q)\land
  t\in prodSigmaDelta(p,q)\land s=Prod.fst''t$.
- `IsPavingAnalytic` p s means
  $\exists K,\ \operatorname{Nonempty}(K)\land \operatorname{IsPavingAnalyticFor}(p,K,s)$.
- `IsPavingAnalyticFor.isPavingAnalytic` forgets the witness K when K is nonempty;
  `isPavingAnalyticFor_of_mem` and `isPavingAnalytic_of_mem` state
  $s\in p\Rightarrow \operatorname{IsPavingAnalyticFor}(p,K,s)$ and
  $s\in p\Rightarrow \operatorname{IsPavingAnalytic}(p,s)$.
- `IsPavingAnalyticFor.mono` and `IsPavingAnalytic.mono` state that
  $p\subseteq p'\Rightarrow \operatorname{IsPavingAnalyticFor}(p,K,s)\Rightarrow
  \operatorname{IsPavingAnalyticFor}(p',K,s)$ and the corresponding implication for
  $\operatorname{IsPavingAnalytic}$.
- `MeasurableSet.of_mem_countableInfClosure` and
  `MeasurableSet.of_mem_countableInfClosure'` show
  $s\in countableInfClosure(p)\Rightarrow MeasurableSet(s)$ when the generators are measurable.
  `MeasurableSet.of_mem_countableSupClosure'` and `MeasurableSet.of_mem_supClosure` give the
  corresponding countable-sup and finite-sup statements.
- `MeasurableSet.of_mem_image2_prod` proves that a product of measurable members of p and q is
  measurable; `MeasurableSet.of_mem_prodSigmaDelta` extends this to
  $s\in prodSigmaDelta(p,q)$.

## References

The definitions and closure results formalize the corresponding arguments in He, Wang, and Yan,
Semimartingale Theory and Stochastic Calculus, first edition, Routledge (1992), Theorems 1.25–1.32,
ISBN 978-0-8493-7715-0.
-/
@[expose] public section

open scoped MeasureTheory
open MeasureTheory

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}

lemma MeasurableSet.of_mem_countableInfClosure {m𝓧 : MeasurableSpace 𝓧} {s : Set 𝓧}
    (hs : s ∈ countableInfClosure {t | MeasurableSet t}) :
    MeasurableSet s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨A, hA, rfl⟩ := hs
  exact MeasurableSet.iInter hA

lemma MeasurableSet.of_mem_countableInfClosure' {m𝓧 : MeasurableSpace 𝓧}
    {s : Set 𝓧} {p : Set (Set 𝓧)} (hs : s ∈ countableInfClosure p) (hp : ∀ t ∈ p, MeasurableSet t) :
    MeasurableSet s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact MeasurableSet.iInter fun n ↦ hp (t n) (ht n)

lemma MeasurableSet.of_mem_countableSupClosure' {m𝓧 : MeasurableSpace 𝓧}
    {s : Set 𝓧} {p : Set (Set 𝓧)} (hs : s ∈ countableSupClosure p) (hp : ∀ t ∈ p, MeasurableSet t) :
    MeasurableSet s := by
  rw [mem_countableSupClosure_iff_iSup] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n ↦ hp (t n) (ht n)

lemma MeasurableSet.of_mem_supClosure {m𝓧 : MeasurableSpace 𝓧} {s : Set 𝓧}
    {p : Set (Set 𝓧)} (hs : s ∈ supClosure p) (hp : ∀ t ∈ p, MeasurableSet t) :
    MeasurableSet s := by
  rw [MeasureTheory.Analytic.mem_supClosure_set_iff] at hs
  obtain ⟨t, _, h_eq, ht⟩ := hs
  rw [h_eq]
  rw [Set.sUnion_eq_biUnion]
  exact MeasurableSet.biUnion (Finset.countable_toSet t) fun A hA ↦ hp A (ht hA)

lemma MeasurableSet.of_mem_image2_prod {Ω 𝓧 : Type*}
    {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {s : Set (𝓧 × Ω)} {p : Set (Set 𝓧)} {q : Set (Set Ω)} (hs : s ∈ Set.image2 (· ×ˢ ·) p q)
    (hp : ∀ t ∈ p, MeasurableSet t) (hq : ∀ t ∈ q, MeasurableSet t) :
    MeasurableSet s := by
  obtain ⟨A, hA, B, hB, rfl⟩ := hs
  exact MeasurableSet.prod (hp A hA) (hq B hB)

lemma MeasurableSet.of_mem_prodSigmaDelta {Ω 𝓧 : Type*}
    {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
    {s : Set (𝓧 × Ω)} {p : Set (Set 𝓧)} {q : Set (Set Ω)}
    (hs : s ∈ prodSigmaDelta p q)
    (hp : ∀ t ∈ p, MeasurableSet t) (hq : ∀ t ∈ q, MeasurableSet t) :
    MeasurableSet s := by
  unfold prodSigmaDelta at hs
  refine MeasurableSet.of_mem_countableInfClosure' hs fun s hs ↦ ?_
  refine MeasurableSet.of_mem_countableSupClosure' hs fun s hs ↦ ?_
  exact MeasurableSet.of_mem_image2_prod hs hp hq


/-- A set `s` is analytic for a paving (predicate) `p` and a type `𝓚` if there exists a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`prodSigmaDelta p q`. -/
def IsPavingAnalyticFor (p : Set (Set 𝓧)) (𝓚 : Type*) (s : Set 𝓧) : Prop :=
  ∃ q : Set (Set 𝓚), ∅ ∈ q ∧ IsCompactSystem q ∧
    ∃ t : Set (𝓧 × 𝓚), t ∈ prodSigmaDelta p q ∧ s = Prod.fst '' t

/-- A set `s` is analytic for a paving (predicate) `p` if there exists a type `𝓚` and a compact
system `q` of `𝓚` such that `s` is the projections of a set `t` that satisfies
`prodSigmaDelta p q`. -/
def IsPavingAnalytic (p : Set (Set 𝓧)) (s : Set 𝓧) : Prop :=
  ∃ 𝓚 : Type, Nonempty 𝓚 ∧ IsPavingAnalyticFor p 𝓚 s

lemma IsPavingAnalyticFor.isPavingAnalytic {𝓚 : Type} [Nonempty 𝓚]
    (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalytic p s := ⟨𝓚, ‹_›, hs⟩

lemma isPavingAnalyticFor_of_mem (𝓚 : Type*) [Nonempty 𝓚] (hs : s ∈ p) :
    IsPavingAnalyticFor p 𝓚 s := by
  classical
  refine ⟨{Set.univ, ∅}, ?_, ?_, ⟨s ×ˢ .univ, ?_, by ext; simp⟩⟩
  · simp
  · exact IsCompactSystem.insert_univ isCompactSystem_singleton_empty
  · exact mem_prodSigmaDelta_of_mem hs (by simp)

lemma isPavingAnalytic_of_mem (hs : s ∈ p) : IsPavingAnalytic p s :=
  (isPavingAnalyticFor_of_mem ℝ hs).isPavingAnalytic

lemma IsPavingAnalyticFor.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsPavingAnalyticFor p' 𝓚 s := by
  obtain ⟨q, hq_empty, hq_compact, t, ht_prod, rfl⟩ := hs
  refine ⟨q, hq_empty, hq_compact, ⟨t, ?_, rfl⟩⟩
  exact prodSigmaDelta.mono hp (fun _ ↦ id) ht_prod

lemma IsPavingAnalytic.mono {p' : Set (Set 𝓧)} (hp : p ⊆ p') (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic p' s := by
  choose 𝓚 h𝓚 hs𝓚 using hs
  exact (IsPavingAnalyticFor.mono hp hs𝓚).isPavingAnalytic

end MeasureTheory.Analytic.Paving

end
