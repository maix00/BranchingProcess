/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.Finite.Partition
public import Mathlib.Probability.Independence.Basic

/-!
# Finite choices based on independent past information

Finite measurable cells of the past can select corresponding future events.
Independence supplies a product formula on each cell, and a uniform lower
bound for the selected future events transfers to their union.

* `measure_finiteAdaptiveChoice_ge_mul` states
  `c * P(past ∈ ⋃ i, U i) ≤ P(∃ i, past ∈ U i ∧ next ∈ V i)` for a finite
  pairwise-disjoint family `U`, with `past` independent of `next` and each
  future event `V i` having probability at least `c`.
* `measure_adaptiveChoice_ge_mul` is the binary version where the choice
  between two future events is determined by a measurable set `S` of pasts.
* `measure_adaptiveSuccess_ge_pow` iterates binary feedback over `n` steps
  and gives `q ^ n ≤ P(past n ∈ U n)`.
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

/-- A past-measurable binary choice between two independent future events
has at least the smaller of their probabilities, conditional on an admissible
past event. -/
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
  let A : Bool → Set Ω := fun b =>
    past ⁻¹' (U ∩ if b then S else Sᶜ)
  let B : Bool → Set Ω := fun b =>
    next ⁻¹' if b then Vminus else Vplus
  have hA : ∀ b, NullMeasurableSet (A b) P := by
    intro b
    change NullMeasurableSet (past ⁻¹' (U ∩ if b then S else Sᶜ)) P
    split_ifs
    · exact hpast.nullMeasurableSet_preimage (hU.inter hS)
    · exact hpast.nullMeasurableSet_preimage (hU.inter hS.compl)
  have hB : ∀ b, NullMeasurableSet (B b) P := by
    intro b
    change NullMeasurableSet (next ⁻¹' if b then Vminus else Vplus) P
    split_ifs
    · exact hnext.nullMeasurableSet_preimage hVminus
    · exact hnext.nullMeasurableSet_preimage hVplus
  have hdisj : Pairwise (fun b c => Disjoint (A b) (A c)) := by
    intro b c hbc
    cases b <;> cases c <;> simp_all [A, Set.disjoint_left]
  have hfactor : ∀ b, P (A b ∩ B b) = P (A b) * P (B b) := by
    intro b
    cases b
    · exact hindep.measure_inter_preimage_eq_mul _ _
        (hU.inter hS.compl) hVplus
    · exact hindep.measure_inter_preimage_eq_mul _ _
        (hU.inter hS) hVminus
  have hlower : ∀ b, q ≤ P (B b) := by
    intro b
    cases b
    · simpa [B] using hqplus
    · simpa [B] using hqminus
  have hbound := measure_iUnion_inter_ge_mul_of_finite_partition
    P A B q hA hB hdisj hfactor hlower
  have hunion : (⋃ b, A b) = past ⁻¹' U := by
    ext ω
    by_cases hs : past ω ∈ S <;>
      simp [A, Set.mem_iUnion, Bool.exists_bool, hs]
  rw [hunion] at hbound
  have hrhs : (⋃ b, A b ∩ B b) =
      ((past ⁻¹' (U ∩ S)) ∩ (next ⁻¹' Vminus)) ∪
        ((past ⁻¹' (U ∩ Sᶜ)) ∩ (next ⁻¹' Vplus)) := by
    ext ω
    simp [A, B, Bool.exists_bool, or_comm]
  rw [hrhs] at hbound
  exact hbound

/-- Finite feedback induction from independence of each fresh block from
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
