/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.Defs.LinearOrder
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.InclusionExclusion
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Rotation.Basic
import Combinatorics.Sequence.CyclicGap.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Tactic.Abel
import Probability.Sequence.IID.Blocks.Consecutive

import all Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Lemmas.BlockProbability.Event

/-!
# Measure identities for adjacent cyclic blocks

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_eq_cyclicBlock_sum`:
  finite inclusion--exclusion expresses the probability of a nonnegative
  endpoint as an alternating sum of adjacent-block events $B_u$.
- `ProbabilityTheory.RandomWalk.cyclicBlockEvent_eq_gapSurvival` identifies
  $B_u$ with survival on each consecutive cyclic gap after rotation.

These are equations (A.4)--(A.5) in Appendix A of M. Bauer, C. Godrèche,
and J.-M. Luck, “Statistics of persistent events in the binomial random walk:
Will the drunken sailor hit the sober man?”, *Journal of Statistical
Physics* 96 (1999), 963--1019, DOI 10.1023/A:1004636216365,
arXiv:cond-mat/9905252.
-/

section

open MeasureTheory

open Combinatorics.Sequence

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]
  [IsOrderedAddMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- Substituting the block decomposition (A.5) into the finite
inclusion--exclusion identity (A.4) of Bauer--Godrèche--Luck,
Appendix A. -/
lemma measureReal_nonnegative_endpoint_eq_cyclicBlock_sum
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    {n : ℕ} (hn : 0 < n) (μ : MeasureTheory.Measure (Fin n → G))
    [MeasureTheory.IsFiniteMeasure μ] :
    μ.real {x : Fin n → G | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset with u.Nonempty,
        (-1 : ℝ) ^ (u.card + 1) *
          μ.real (if h : u.Nonempty then cyclicBlockEvent u h else ∅) := by
  rw [measureReal_nonnegative_endpoint_eq_cyclicSurvival_sum hIci hn μ]
  apply Finset.sum_congr rfl
  intro u hu
  have hnonempty : u.Nonempty := (Finset.mem_filter.mp hu).2
  simp only [dite_eq_left hnonempty]
  rw [iInter_cyclicSurvivalEvent_eq_cyclicBlockEvent u hnonempty]


omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- Each block in the adjacent-block event is a surviving walk segment.
This is the forward direction in the probability factorization (A.6). -/
private lemma cyclicBlockEvent_gapSurvival {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → G) (hx : x ∈ cyclicBlockEvent u hu)
    (j : Fin u.card) (t : Fin (cyclicGapLength u hu j + 1)) :
    0 ≤ Fin.partialSum (cyclicGapCoordinates u hu x j) t := by
  rw [partialSum_cyclicGapCoordinates u hu x j t]
  have hselected := forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent x u hu hx
    (u.orderEmbOfFin rfl j) (u.orderEmbOfFin_mem rfl j)
  exact hselected ⟨t.val, by
    have hbound := blockStart_add_cyclicGapLength_le u hu j
    omega⟩

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- If every adjacent cyclic block survives, the original prefix path
satisfies the adjacent-block inequalities of (A.5). -/
private lemma cyclicBlockEvent_of_gapSurvival {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → G)
    (hx : ∀ j : Fin u.card,
      ∀ t : Fin (cyclicGapLength u hu j + 1),
        0 ≤ Fin.partialSum (cyclicGapCoordinates u hu x j) t) :
    x ∈ cyclicBlockEvent u hu := by
  let starts := u.orderEmbOfFin rfl
  let first : Fin u.card := ⟨0, Finset.card_pos.mpr hu⟩
  let last : Fin u.card :=
    ⟨u.card - 1, Nat.sub_lt (Finset.card_pos.mpr hu) (Nat.succ_pos 0)⟩
  have hfirst : starts first = u.min' hu := by
    simpa [starts, first] using
      (Finset.orderEmbOfFin_zero (s := u) rfl (Finset.card_pos.mpr hu))
  have hlast : starts last = u.max' hu := by
    simpa [starts, last] using
      (Finset.orderEmbOfFin_last (s := u) rfl (Finset.card_pos.mpr hu))
  intro t
  by_cases hpred : (precedingStarts u t).Nonempty
  · let p := (precedingStarts u t).max' hpred
    have hpMem : p ∈ u :=
      (Finset.mem_filter.mp ((precedingStarts u t).max'_mem hpred)).1
    have hpt : p.val < t.val :=
      (Finset.mem_filter.mp ((precedingStarts u t).max'_mem hpred)).2
    let j : Fin u.card := (u.orderIsoOfFin rfl).symm ⟨p, hpMem⟩
    have hj : starts j = p := by
      dsimp [starts, j]
      exact congrArg Subtype.val
        ((u.orderIsoOfFin rfl).apply_symm_apply ⟨p, hpMem⟩)
    have hdistance : t.val - p.val ≤ cyclicGapLength u hu j := by
      by_cases hnext : j.val + 1 < u.card
      · let next : Fin u.card := ⟨j.val + 1, hnext⟩
        have hjnext : p < starts next := by
          rw [← hj]
          exact starts.strictMono (Fin.lt_def.mpr (Nat.lt_succ_self _))
        have htNext : t.val ≤ (starts next).val := by
          by_contra h
          have hnextMem : starts next ∈ precedingStarts u t :=
            Finset.mem_filter.mpr
              ⟨u.orderEmbOfFin_mem rfl next, by omega⟩
          have hpMax := (precedingStarts u t).le_max' _ hnextMem
          exact (not_lt_of_ge hpMax) hjnext
        have hgap : cyclicGapLength u hu j =
            (starts next).val - p.val := by
          rw [← hj]
          simp only [cyclicGapLength, cyclicGapLengthAt,
            dite_eq_left j.isLt, dite_eq_left hnext]
          rfl
        rw [hgap]
        omega
      · have hgap : cyclicGapLength u hu j =
            n - p.val + (starts first).val := by
          rw [← hj]
          simp only [cyclicGapLength, cyclicGapLengthAt,
            dite_eq_left j.isLt, dite_eq_right hnext]
          rfl
        rw [hgap]
        have hpN := p.isLt
        have htN := Nat.le_of_lt_succ t.isLt
        omega
    let d : Fin (cyclicGapLength u hu j + 1) :=
      ⟨t.val - p.val, Nat.lt_succ_of_le hdistance⟩
    have hlocal := hx j d
    rw [partialSum_cyclicGapCoordinates u hu x j d, hj] at hlocal
    have hsum : p.val + d.val ≤ n := by
      dsimp [d]
      have htN := Nat.le_of_lt_succ t.isLt
      omega
    have hindex :
        (⟨p.val + d.val, Nat.lt_succ_of_le hsum⟩ : Fin (n + 1)) = t := by
      apply Fin.ext
      dsimp [d]
      omega
    have hineq : Fin.partialSum x p.castSucc ≤ Fin.partialSum x t := by
      simp only [Fin.cyclicPartialSum, dite_eq_left hsum, hindex] at hlocal
      exact sub_nonneg.mp hlocal
    simpa [cyclicBlockEvent, hpred, p] using hineq
  · have htFirst : t.val ≤ (starts first).val := by
      by_contra h
      have hmem : starts first ∈ precedingStarts u t :=
        Finset.mem_filter.mpr
          ⟨u.orderEmbOfFin_mem rfl first, by omega⟩
      exact hpred ⟨starts first, hmem⟩
    have hgap : cyclicGapLength u hu last =
        n - (starts last).val + (starts first).val := by
      simp only [cyclicGapLength, cyclicGapLengthAt,
        dite_eq_left last.isLt,
        dite_eq_right (by dsimp [last]; omega : ¬ last.val + 1 < u.card)]
      rfl
    have hd : n - (starts last).val + t.val ≤
        cyclicGapLength u hu last := by
      rw [hgap]
      omega
    let d : Fin (cyclicGapLength u hu last + 1) :=
      ⟨n - (starts last).val + t.val, Nat.lt_succ_of_le hd⟩
    have hlocal := hx last d
    rw [partialSum_cyclicGapCoordinates u hu x last d] at hlocal
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) (starts last)
      (⟨d.val, by
        have hbound := blockStart_add_cyclicGapLength_le u hu last
        omega⟩ : Fin (n + 1)) at hlocal
    have hlastN := (starts last).isLt
    have htarget : Fin.partialSum x (u.max' hu).castSucc ≤
        Fin.partialSum x (Fin.last n) + Fin.partialSum x t := by
      rw [← hlast]
      by_cases htZero : t.val = 0
      · have ht : t = 0 := Fin.ext htZero
        subst t
        have hsum : (starts last).val + d.val ≤ n := by
          dsimp [d]
          omega
        have hindex :
            (⟨(starts last).val + d.val, Nat.lt_succ_of_le hsum⟩ : Fin (n + 1)) =
              Fin.last n := by
          apply Fin.ext
          dsimp [d]
          omega
        simp only [Fin.cyclicPartialSum, dite_eq_left hsum, hindex,
          Fin.partialSum_zero, add_zero] at hlocal ⊢
        exact sub_nonneg.mp hlocal
      · have hsum : ¬ (starts last).val + d.val ≤ n := by
          dsimp [d]
          omega
        have hindex :
            (⟨(starts last).val + d.val - n, by omega⟩ : Fin (n + 1)) =
              t := by
          apply Fin.ext
          dsimp [d]
          omega
        simp only [Fin.cyclicPartialSum, dite_eq_right hsum, hindex] at hlocal
        exact le_of_nonneg_sub_add _ _ _ hlocal
    simpa [cyclicBlockEvent, hpred, hlast] using htarget

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- The event identity behind Bauer--Godrèche--Luck, Appendix A,
equation (A.6): the intersection of selected cyclic survival events is
the survival event of every disjoint consecutive block after one rotation. -/
lemma cyclicBlockEvent_eq_gapSurvival {n : ℕ}
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    cyclicBlockEvent u hu =
      {x : Fin n → G | ∀ j : Fin u.card,
        ∀ t : Fin (cyclicGapLength u hu j + 1),
          0 ≤ Fin.partialSum (cyclicGapCoordinates u hu x j) t} := by
  ext x
  constructor
  · intro hx j t
    exact cyclicBlockEvent_gapSurvival u hu x hx j t
  · intro hx
    exact cyclicBlockEvent_of_gapSurvival u hu x hx

end ProbabilityTheory.RandomWalk

end
