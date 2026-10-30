/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import MeasureTheory.Measure.Partition
public import Mathlib.Probability.Independence.Basic

/-!
# Adaptive choices based on independent future information

Finite measurable cells of the past can select corresponding future events.
Independence supplies a product formula on each cell, and a uniform lower
bound for the selected future events transfers to their union.

## Public declarations

- `ProbabilityTheory.measure_finiteAdaptiveChoice_ge_mul`: if a.e.-measurable
  functions `past` and `next` are independent and a finite pairwise-disjoint
  family of measurable past cells $U_i$ selects measurable future events
  $V_i$ with $c\le P(next\in V_i)$, then
  $cP(past\in\bigcup_iU_i)\le
  P(\bigcup_i(past\in U_i\land next\in V_i))$.
- `ProbabilityTheory.measure_adaptiveChoice_ge_mul`: for a.e.-measurable
  independent `past` and `next`, if the binary choice is determined by a
  measurable past event $S$, then
  $qP(past\in U)\le P((past\in U\cap S\land next\in V_-)
  \lor(past\in U\cap S^c\land next\in V_+))$ when both future events have
  probability at least $q$.
- `ProbabilityTheory.measure_adaptiveSuccess_ge_pow`: if each a.e.-measurable
  `next k` is independent of `past k`, the initial event has measure $1$, and
  every binary success at step $k$ implies the event at step $k+1$, then
  $q^n\le P(past\ n\in U_n)$.
- `ProbabilityTheory.measure_adaptiveSuccess_ge_pow_of_factorization`: if
  $P(A_k\cap S_k\cap B_k^-)=P(A_k\cap S_k)p_k^-$ and
  $P(A_k\cap S_k^c\cap B_k^+)=P(A_k\cap S_k^c)p_k^+$, where
  $p_k^\pm\ge q$, and the two successful branches imply $A_{k+1}$, then
  $q^n\le P(A_n)$. The branch probabilities may vary with $k$.
- `ProbabilityTheory.measure_adaptiveSuccess_pos_of_factorization`: a positive
  uniform branch bound $q>0$ makes every finite adaptive-success event
  positive.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- A finite pairwise-disjoint family of admissible past events selects the
corresponding future event. If past and future are independent, and each
selected future event has probability at least `c`, then the probability of a
successful selection is at least `c` times the probability of the union of
the past cells. -/
theorem measure_finiteAdaptiveChoice_ge_mul
    {Ω Past Future ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Past] [MeasurableSpace Future] [Fintype ι]
    (P : Measure Ω) (past : Ω → Past) (next : Ω → Future)
    (hindep : past ⟂ᵢ[P] next)
    (hpast : AEMeasurable past P) (hnext : AEMeasurable next P)
    (U : ι → Set Past) (V : ι → Set Future) (c : ENNReal)
    (hU : ∀ i, MeasurableSet (U i))
    (hV : ∀ i, MeasurableSet (V i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hc : ∀ i, c ≤ P (next ⁻¹' V i)) :
    c * P (⋃ i, past ⁻¹' U i) ≤
      P (⋃ i, past ⁻¹' U i ∩ next ⁻¹' V i) := by
  let A : ι → Set Ω := fun i => past ⁻¹' U i
  let B : ι → Set Ω := fun i => next ⁻¹' V i
  have hA : ∀ i, NullMeasurableSet (A i) P := by
    intro i
    exact hpast.nullMeasurableSet_preimage (hU i)
  have hB : ∀ i, NullMeasurableSet (B i) P := by
    intro i
    exact hnext.nullMeasurableSet_preimage (hV i)
  have hdisj' : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    exact (hdisj hij).preimage past
  have hfactor : ∀ i, P (A i ∩ B i) = P (A i) * P (B i) := by
    intro i
    exact hindep.measure_inter_preimage_eq_mul _ _ (hU i) (hV i)
  have hlower : ∀ i, c ≤ P (B i) := hc
  exact measure_iUnion_inter_ge_mul_of_finite_partition P A B c
    hA hB hdisj' hfactor hlower

/-- If a measurable past event is split into two disjoint cells and each cell
selects an independent future event of measure at least `q`, the measure of
the union of successful choices is at least `q` times the measure of the
original past event. -/
theorem measure_adaptiveChoice_ge_mul
    {Ω Past Future : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Past] [MeasurableSpace Future]
    (P : Measure Ω) (past : Ω → Past) (next : Ω → Future)
    (hindep : past ⟂ᵢ[P] next)
    (hpast : AEMeasurable past P) (hnext : AEMeasurable next P)
    (U S : Set Past) (Vplus Vminus : Set Future)
    (hU : MeasurableSet U) (hS : MeasurableSet S)
    (hVplus : MeasurableSet Vplus) (hVminus : MeasurableSet Vminus)
    (q : ENNReal)
    (hqplus : q ≤ P (next ⁻¹' Vplus))
    (hqminus : q ≤ P (next ⁻¹' Vminus)) :
    q * P (past ⁻¹' U) ≤
      P (((past ⁻¹' (U ∩ S)) ∩ (next ⁻¹' Vminus)) ∪
        ((past ⁻¹' (U ∩ Sᶜ)) ∩ (next ⁻¹' Vplus))) := by
  let U' : Bool → Set Past := fun b =>
    U ∩ if b then S else Sᶜ
  let V' : Bool → Set Future := fun b =>
    if b then Vminus else Vplus
  have hU' : ∀ b, MeasurableSet (U' b) := by
    intro b
    cases b
    · simpa [U'] using hU.inter hS.compl
    · simpa [U'] using hU.inter hS
  have hV' : ∀ b, MeasurableSet (V' b) := by
    intro b
    cases b
    · simpa [V'] using hVplus
    · simpa [V'] using hVminus
  have hdisj : Pairwise (fun b c => Disjoint (U' b) (U' c)) := by
    intro b c hbc
    cases b <;> cases c <;> simp_all [U', Set.disjoint_left]
  have hq : ∀ b, q ≤ P (next ⁻¹' V' b) := by
    intro b
    cases b
    · simpa [V'] using hqplus
    · simpa [V'] using hqminus
  have hbound := measure_finiteAdaptiveChoice_ge_mul P past next
    hindep hpast hnext U' V' q hU' hV' hdisj hq
  have hunion : (⋃ b, past ⁻¹' U' b) = past ⁻¹' U := by
    ext ω
    by_cases hs : past ω ∈ S <;>
      simp [U', Set.mem_iUnion, Bool.exists_bool, hs]
  rw [hunion] at hbound
  have hrhs : (⋃ b, past ⁻¹' U' b ∩ next ⁻¹' V' b) =
      ((past ⁻¹' (U ∩ S)) ∩ (next ⁻¹' Vminus)) ∪
        ((past ⁻¹' (U ∩ Sᶜ)) ∩ (next ⁻¹' Vplus)) := by
    ext ω
    simp [U', V', Bool.exists_bool, or_comm]
  rw [hrhs] at hbound
  exact hbound

/-- Event-level adaptive induction from the two branch-factorization
identities. At each step, `success k ∩ sign k` selects `minus k`, while
`success k ∩ (sign k)ᶜ` selects `plus k`; if both corresponding branch
probabilities are at least `q`, then `success n` has probability at least
`q ^ n`. The branch probabilities may vary with the step. -/
theorem measure_adaptiveSuccess_ge_pow_of_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (success sign plus minus : ℕ → Set Ω)
    (q : ENNReal) (qPlus qMinus : ℕ → ENNReal)
    (hqPlus : ∀ k, q ≤ qPlus k) (hqMinus : ∀ k, q ≤ qMinus k)
    (hzero : P (success 0) = 1)
    (hmeasSuccess : ∀ k, MeasurableSet (success k))
    (hmeasSign : ∀ k, MeasurableSet (sign k))
    (hmeasPlus : ∀ k, MeasurableSet (plus k))
    (hmeasMinus : ∀ k, MeasurableSet (minus k))
    (hstep : ∀ k,
      (success k ∩ sign k ∩ minus k) ∪
        (success k ∩ (sign k)ᶜ ∩ plus k) ⊆ success (k + 1))
    (hprodMinus : ∀ k,
      P (success k ∩ sign k ∩ minus k) =
        P (success k ∩ sign k) * qMinus k)
    (hprodPlus : ∀ k,
      P (success k ∩ (sign k)ᶜ ∩ plus k) =
        P (success k ∩ (sign k)ᶜ) * qPlus k) :
    ∀ n, q ^ n ≤ P (success n) := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ k ih =>
    let A := success k ∩ sign k ∩ minus k
    let B := success k ∩ (sign k)ᶜ ∩ plus k
    have hdisjoint : Disjoint A B := by
      apply Set.disjoint_left.mpr
      intro ω hA hB
      exact hB.1.2 hA.1.2
    have hmeasA : MeasurableSet A :=
      ((hmeasSuccess k).inter (hmeasSign k)).inter (hmeasMinus k)
    have hmeasB : MeasurableSet B :=
      ((hmeasSuccess k).inter ((hmeasSign k).compl)).inter (hmeasPlus k)
    have hsplit : P (success k ∩ sign k) +
        P (success k ∩ (sign k)ᶜ) = P (success k) := by
      rw [← measure_union]
      · congr 1
        ext ω
        simp
      · exact Set.disjoint_left.mpr (by
          intro ω hω hω'
          exact hω'.2 hω.2)
      · exact (hmeasSuccess k).inter ((hmeasSign k).compl)
    have hbound : P (success k) * q ≤ P (A ∪ B) := by
      rw [measure_union hdisjoint hmeasB, hprodMinus k, hprodPlus k,
        ← hsplit]
      rw [add_mul]
      exact add_le_add
        (by simpa [mul_comm] using
          mul_le_mul_right (hqMinus k) (P (success k ∩ sign k)))
        (by simpa [mul_comm] using
          mul_le_mul_right (hqPlus k) (P (success k ∩ (sign k)ᶜ)))
    calc
      q ^ (k + 1) = q ^ k * q := pow_succ q k
      _ ≤ P (success k) * q := by
        simpa [mul_comm] using mul_le_mul_right ih q
      _ ≤ P (A ∪ B) := hbound
      _ ≤ P (success (k + 1)) := measure_mono (hstep k)

/-- A positive uniform branch bound gives positive probability to every
finite adaptive-success event under the same factorization assumptions. -/
theorem measure_adaptiveSuccess_pos_of_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (success sign plus minus : ℕ → Set Ω)
    (q : ENNReal) (qPlus qMinus : ℕ → ENNReal) (hq : 0 < q)
    (hqPlus : ∀ k, q ≤ qPlus k) (hqMinus : ∀ k, q ≤ qMinus k)
    (hzero : P (success 0) = 1)
    (hmeasSuccess : ∀ k, MeasurableSet (success k))
    (hmeasSign : ∀ k, MeasurableSet (sign k))
    (hmeasPlus : ∀ k, MeasurableSet (plus k))
    (hmeasMinus : ∀ k, MeasurableSet (minus k))
    (hstep : ∀ k,
      (success k ∩ sign k ∩ minus k) ∪
        (success k ∩ (sign k)ᶜ ∩ plus k) ⊆ success (k + 1))
    (hprodMinus : ∀ k,
      P (success k ∩ sign k ∩ minus k) =
        P (success k ∩ sign k) * qMinus k)
    (hprodPlus : ∀ k,
      P (success k ∩ (sign k)ᶜ ∩ plus k) =
        P (success k ∩ (sign k)ᶜ) * qPlus k)
    (n : ℕ) : 0 < P (success n) :=
  (ENNReal.pow_pos hq n).trans_le
    (measure_adaptiveSuccess_ge_pow_of_factorization P success sign plus minus
      q qPlus qMinus hqPlus hqMinus hzero hmeasSuccess hmeasSign hmeasPlus
      hmeasMinus hstep hprodMinus hprodPlus n)

/-- Adaptive-choice induction from independence of each fresh block from
the information used to select it. No independence is assumed for the
adaptively selected event itself. -/
theorem measure_adaptiveSuccess_ge_pow
    {Ω Past Future : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Past] [MeasurableSpace Future]
    (P : Measure Ω) (past : ℕ → Ω → Past) (next : ℕ → Ω → Future)
    (U S : ℕ → Set Past) (Vplus Vminus : ℕ → Set Future)
    (q : ENNReal)
    (hzero : P (past 0 ⁻¹' U 0) = 1)
    (hindep : ∀ k, past k ⟂ᵢ[P] next k)
    (hpast : ∀ k, AEMeasurable (past k) P)
    (hnext : ∀ k, AEMeasurable (next k) P)
    (hU : ∀ k, MeasurableSet (U k))
    (hS : ∀ k, MeasurableSet (S k))
    (hVplus : ∀ k, MeasurableSet (Vplus k))
    (hVminus : ∀ k, MeasurableSet (Vminus k))
    (hqplus : ∀ k, q ≤ P (next k ⁻¹' Vplus k))
    (hqminus : ∀ k, q ≤ P (next k ⁻¹' Vminus k))
    (hstep : ∀ k,
      ((past k ⁻¹' (U k ∩ S k)) ∩ (next k ⁻¹' Vminus k)) ∪
        ((past k ⁻¹' (U k ∩ (S k)ᶜ)) ∩ (next k ⁻¹' Vplus k)) ⊆
          past (k + 1) ⁻¹' U (k + 1)) :
    ∀ n, q ^ n ≤ P (past n ⁻¹' U n) := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ k ih =>
    have hchoice := measure_adaptiveChoice_ge_mul P (past k) (next k)
      (hindep k) (hpast k) (hnext k)
      (U k) (S k) (Vplus k) (Vminus k)
      (hU k) (hS k) (hVplus k) (hVminus k) q
      (hqplus k) (hqminus k)
    calc
      q ^ (k + 1) = q * q ^ k := pow_succ' q k
      _ ≤ q * P (past k ⁻¹' U k) := by
        simpa [mul_comm] using mul_le_mul_left ih q
      _ ≤ P (((past k ⁻¹' (U k ∩ S k)) ∩
          (next k ⁻¹' Vminus k)) ∪
          ((past k ⁻¹' (U k ∩ (S k)ᶜ)) ∩
          (next k ⁻¹' Vplus k))) := hchoice
      _ ≤ P (past (k + 1) ⁻¹' U (k + 1)) :=
        measure_mono (hstep k)

end ProbabilityTheory

end
