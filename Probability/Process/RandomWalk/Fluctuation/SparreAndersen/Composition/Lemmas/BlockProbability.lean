/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.InclusionExclusion
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Cyclic
import Probability.Process.RandomWalk.Path.Block.Law.FiniteProduct
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Tactic.Abel
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Private proof steps for the cyclic gap identity

This module has no public declarations.

This module contains the event decomposition and block factorization used to
prove the public cyclic gap identity in `CyclicGapSum.lean`. The statements
are specific to this proof chain. The identity is equation (A.6) of
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events in
the binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, *Journal of Statistical Physics* 96 (1999), 963--1019, DOI
10.1023/A:1004636216365, arXiv:cond-mat/9905252.
-/

section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]
  [IsOrderedAddMonoid G]

/-- Reordering a cyclic partial-sum difference into the corresponding
endpoint comparison in an ordered additive group. -/
private lemma le_of_nonneg_sub_add (a b c : G)
    (h : 0 ≤ a - b + c) : b ≤ a + c := by
  have heq : a - b + c = a + c - b := by abel
  have h' : 0 ≤ a + c - b := by
    rw [← heq]
    exact h
  exact sub_nonneg.mp h'

/-- The converse comparison, expressed as a nonnegative cyclic increment. -/
private lemma nonneg_sub_add_of_le (a b c : G)
    (h : b ≤ a + c) : 0 ≤ a - b + c := by
  have h' : 0 ≤ a + c - b := sub_nonneg.mpr h
  have heq : a - b + c = a + c - b := by abel
  rw [heq]
  exact h'

/-- A surviving rotation has nonnegative partial sums from its start
up to every later time before the end of the original vector. -/
private lemma cyclicSurvivalEvent_partialSum_le_of_start_le
    {n : ℕ} (x : Fin n → G) (k : Fin n) (t : Fin (n + 1))
    (hkt : k.val ≤ t.val) (hx : x ∈ cyclicSurvivalEvent k) :
    Fin.partialSum x k.castSucc ≤ Fin.partialSum x t := by
  let j : Fin (n + 1) := ⟨t.val - k.val, by omega⟩
  have hsum : k.val + j.val ≤ n := by dsimp [j]; omega
  have hindex :
      (⟨k.val + j.val, Nat.lt_succ_of_le hsum⟩ : Fin (n + 1)) = t := by
    apply Fin.ext
    dsimp [j]
    omega
  have hj := hx j
  change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j at hj
  simp only [Fin.cyclicPartialSum, dite_eq_left hsum, hindex] at hj
  exact sub_nonneg.mp hj

/-- A surviving rotation has nonnegative wrapped partial sums after
reaching the end of the original vector. -/
private lemma cyclicSurvivalEvent_partialSum_le_of_before_start
    {n : ℕ} (x : Fin n → G) (k : Fin n) (t : Fin (n + 1))
    (htk : t.val < k.val) (hx : x ∈ cyclicSurvivalEvent k) :
    Fin.partialSum x k.castSucc ≤
      Fin.partialSum x (Fin.last n) + Fin.partialSum x t := by
  by_cases htzero : t.val = 0
  · have ht : t = 0 := Fin.ext htzero
    subst t
    have hlast := cyclicSurvivalEvent_partialSum_le_of_start_le
      x k (Fin.last n) (by simp [Fin.val_last, Nat.le_of_lt k.isLt]) hx
    simpa using hlast
  · let j : Fin (n + 1) := ⟨n - k.val + t.val, by omega⟩
    have hwrap : ¬ k.val + j.val ≤ n := by dsimp [j]; omega
    have hindex :
        (⟨k.val + j.val - n, by omega⟩ : Fin (n + 1)) = t := by
      apply Fin.ext
      dsimp [j]
      omega
    have hj := hx j
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j at hj
    simp only [Fin.cyclicPartialSum, dite_eq_right hwrap, hindex] at hj
    exact le_of_nonneg_sub_add _ _ _ hj

/-- The explicit two-part description of the cyclic event $B_n^{k+1}$
in Bauer--Godrèche--Luck, Appendix A, equation (A.3). -/
private lemma mem_cyclicSurvivalEvent_iff_partialSum
    {n : ℕ} (x : Fin n → G) (k : Fin n) :
    x ∈ cyclicSurvivalEvent k ↔
      0 ≤ Fin.partialSum x (Fin.last n) ∧
      (∀ t : Fin (n + 1), k.val ≤ t.val →
        Fin.partialSum x k.castSucc ≤ Fin.partialSum x t) ∧
      (∀ t : Fin (n + 1), t.val < k.val →
        Fin.partialSum x k.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x t) := by
  constructor
  · intro hx
    have hlast := hx (Fin.last n)
    change 0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k (Fin.last n) at hlast
    rw [Fin.cyclicPartialSum_last_eq_of_zero
      (Fin.partialSum x) (Fin.partialSum_zero x) k] at hlast
    exact ⟨hlast, fun t hkt =>
      cyclicSurvivalEvent_partialSum_le_of_start_le x k t hkt hx,
      fun t htk =>
        cyclicSurvivalEvent_partialSum_le_of_before_start x k t htk hx⟩
  · rintro ⟨hlast, hfirst, hsecond⟩
    intro j
    by_cases hjlast : j = Fin.last n
    · subst j
      simpa [Fin.cyclicPartialSum_last_eq_of_zero
        (Fin.partialSum x) (Fin.partialSum_zero x) k] using hlast
    by_cases hsum : k.val + j.val ≤ n
    · let t : Fin (n + 1) :=
        ⟨k.val + j.val, Nat.lt_succ_of_le hsum⟩
      have hkt : k.val ≤ t.val := by dsimp [t]; omega
      have h := hfirst t hkt
      have hnonneg :
          0 ≤ Fin.partialSum x t - Fin.partialSum x k.castSucc := by
        exact sub_nonneg.mpr h
      simpa only [cyclicSurvivalEvent, Fin.cyclicPartialSum,
        dite_eq_left hsum] using hnonneg
    · let t : Fin (n + 1) :=
        ⟨k.val + j.val - n, by omega⟩
      have htk : t.val < k.val := by
        dsimp [t]
        have hj : j.val < n := by
          have hjle : j.val ≤ n := Nat.le_of_lt_succ j.isLt
          have hjne : j.val ≠ n := by
            intro heq
            exact hjlast (Fin.ext (by simpa [Fin.val_last] using heq))
          omega
        omega
      have h := hsecond t htk
      have hnonneg :
          0 ≤ Fin.partialSum x (Fin.last n) -
            Fin.partialSum x k.castSucc + Fin.partialSum x t := by
        exact nonneg_sub_add_of_le _ _ _ h
      simpa only [Fin.cyclicPartialSum, dite_eq_right hsum] using hnonneg

/-- The two-start case of Bauer--Godrèche--Luck, Appendix A,
equation (A.5): the intersection of two cyclic survival events is the
product condition on the two consecutive cyclic blocks. -/
private lemma mem_two_cyclicSurvivalEvents_iff_twoBlocks
    {n : ℕ} (x : Fin n → G) (a b : Fin n) (hab : a < b) :
    x ∈ cyclicSurvivalEvent a ∧ x ∈ cyclicSurvivalEvent b ↔
      (∀ t : Fin (n + 1), a.val ≤ t.val → t.val ≤ b.val →
        Fin.partialSum x a.castSucc ≤ Fin.partialSum x t) ∧
      (∀ t : Fin (n + 1), b.val ≤ t.val →
        Fin.partialSum x b.castSucc ≤ Fin.partialSum x t) ∧
      (∀ t : Fin (n + 1), t.val ≤ a.val →
        Fin.partialSum x b.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x t) := by
  have habval : a.val < b.val := hab
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨_, haFirst, _⟩ :=
      (mem_cyclicSurvivalEvent_iff_partialSum x a).mp ha
    obtain ⟨_, hbFirst, hbSecond⟩ :=
      (mem_cyclicSurvivalEvent_iff_partialSum x b).mp hb
    refine ⟨fun t hat _ => haFirst t hat,
      hbFirst, fun t hta => ?_⟩
    exact hbSecond t (by omega)
  · rintro ⟨hfirstBlock, hsecondBlock, hwrapBlock⟩
    have hAB : Fin.partialSum x a.castSucc ≤
        Fin.partialSum x b.castSucc :=
      hfirstBlock b.castSucc (Nat.le_of_lt habval) le_rfl
    have hwrapAtA : Fin.partialSum x b.castSucc ≤
        Fin.partialSum x (Fin.last n) +
          Fin.partialSum x a.castSucc :=
      hwrapBlock a.castSucc le_rfl
    have hlast : 0 ≤ Fin.partialSum x (Fin.last n) := by
      have hle : Fin.partialSum x a.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x a.castSucc :=
        hAB.trans hwrapAtA
      have hsub : 0 ≤
          (Fin.partialSum x (Fin.last n) + Fin.partialSum x a.castSucc) -
            Fin.partialSum x a.castSucc := sub_nonneg.mpr hle
      simpa using hsub
    constructor
    · apply (mem_cyclicSurvivalEvent_iff_partialSum x a).mpr
      refine ⟨hlast, ?_, ?_⟩
      · intro t hat
        by_cases htb : t.val ≤ b.val
        · exact hfirstBlock t hat htb
        · have hbt : b.val ≤ t.val := by omega
          have hb := hsecondBlock t hbt
          exact hAB.trans hb
      · intro t hta
        have hb := hwrapBlock t (Nat.le_of_lt hta)
        exact hAB.trans hb
    · apply (mem_cyclicSurvivalEvent_iff_partialSum x b).mpr
      refine ⟨hlast, hsecondBlock, ?_⟩
      intro t htb
      by_cases hta : t.val ≤ a.val
      · exact hwrapBlock t hta
      · have hat : a.val ≤ t.val := by omega
        have htb' : t.val ≤ b.val := Nat.le_of_lt htb
        have ha := hfirstBlock t hat htb'
        have hna : Fin.partialSum x (Fin.last n) +
            Fin.partialSum x a.castSucc ≤
              Fin.partialSum x (Fin.last n) + Fin.partialSum x t :=
          by
            simpa [add_comm] using
              add_le_add_right ha (Fin.partialSum x (Fin.last n))
        exact hwrapAtA.trans hna

/-- The selected start positions strictly before time `t`. -/
private def precedingStarts {n : ℕ} (u : Finset (Fin n))
    (t : Fin (n + 1)) : Finset (Fin n) :=
  u.filter fun k => k.val < t.val

/-- The adjacent-block event from Bauer--Godrèche--Luck, Appendix A,
equation (A.5), indexed by a nonempty finite set of cyclic starts. At
time `t`, the predecessor in `u` gives the current block; before the
first start, the last block wraps across time `n`. -/
private def cyclicBlockEvent {n : ℕ} (u : Finset (Fin n))
    (hu : u.Nonempty) : Set (Fin n → G) :=
  {x | ∀ t : Fin (n + 1),
    if h : (precedingStarts u t).Nonempty then
      Fin.partialSum x ((precedingStarts u t).max' h).castSucc ≤
        Fin.partialSum x t
    else
      Fin.partialSum x (u.max' hu).castSucc ≤
        Fin.partialSum x (Fin.last n) + Fin.partialSum x t}

/-- Each selected cyclic survival event supplies the corresponding
adjacent-block inequalities. This is the immediate direction of
Bauer--Godrèche--Luck, Appendix A, equation (A.5). -/
private lemma mem_cyclicBlockEvent_of_forall_cyclicSurvivalEvent
    {n : ℕ} (x : Fin n → G) (u : Finset (Fin n))
    (hu : u.Nonempty)
    (hx : ∀ k ∈ u, x ∈ cyclicSurvivalEvent k) :
    x ∈ cyclicBlockEvent u hu := by
  intro t
  by_cases hpred : (precedingStarts u t).Nonempty
  · have hp := (precedingStarts u t).max'_mem hpred
    have hpu : (precedingStarts u t).max' hpred ∈ u :=
      (Finset.mem_filter.mp hp).1
    have hpt : ((precedingStarts u t).max' hpred).val < t.val :=
      (Finset.mem_filter.mp hp).2
    have hle := cyclicSurvivalEvent_partialSum_le_of_start_le
      x ((precedingStarts u t).max' hpred) t
      (Nat.le_of_lt hpt) (hx _ hpu)
    simpa [cyclicBlockEvent, hpred] using hle
  · let m := u.max' hu
    have hmU : m ∈ u := u.max'_mem hu
    have htm : t.val ≤ m.val := by
      by_contra hgt
      have hmPred : m ∈ precedingStarts u t :=
        Finset.mem_filter.mpr ⟨hmU, by omega⟩
      exact hpred ⟨m, hmPred⟩
    have hB := hx m hmU
    by_cases hlt : t.val < m.val
    · have hle := cyclicSurvivalEvent_partialSum_le_of_before_start
        x m t hlt hB
      simpa [cyclicBlockEvent, hpred, m] using hle
    · have hEq : t = m.castSucc := Fin.ext (by simp; omega)
      have hlast := (mem_cyclicSurvivalEvent_iff_partialSum x m).mp hB |>.1
      have hle : Fin.partialSum x m.castSucc ≤
          Fin.partialSum x (Fin.last n) + Fin.partialSum x t := by
        rw [hEq]
        simpa using add_le_add_right hlast (Fin.partialSum x m.castSucc)
      simpa [cyclicBlockEvent, hpred, m] using hle

omit [IsOrderedAddMonoid G] in
/-- Adjacent-block survival makes the partial sums at selected block
starts nondecreasing. -/
private lemma cyclicBlockEvent_selected_partialSum_mono
    {n : ℕ} (x : Fin n → G) (u : Finset (Fin n))
    (hu : u.Nonempty) (hx : x ∈ cyclicBlockEvent u hu)
    {a b : Fin n} (ha : a ∈ u) (hb : b ∈ u) (hab : a ≤ b) :
    Fin.partialSum x a.castSucc ≤ Fin.partialSum x b.castSucc := by
  have hmono (l : Fin n) :
      ∀ (hl : l ∈ u) (k : Fin n), k ∈ u → k ≤ l →
        Fin.partialSum x k.castSucc ≤ Fin.partialSum x l.castSucc := by
    induction l using Fin.strong_induction_on with
    | h l ih =>
      intro hl k hk hkl
      by_cases hEq : k = l
      · subst k
        exact le_refl _
      have hklStrict : k < l := lt_of_le_of_ne hkl hEq
      have hpred : (precedingStarts u l.castSucc).Nonempty := by
        refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩⟩
        exact hklStrict
      let p := (precedingStarts u l.castSucc).max' hpred
      have hpMem := (precedingStarts u l.castSucc).max'_mem hpred
      have hpU : p ∈ u := (Finset.mem_filter.mp hpMem).1
      have hpLt : p < l := (Finset.mem_filter.mp hpMem).2
      have hkp : k ≤ p :=
        (precedingStarts u l.castSucc).le_max' k
          (Finset.mem_filter.mpr ⟨hk, hklStrict⟩)
      have hlocal := hx l.castSucc
      have hpl : Fin.partialSum x p.castSucc ≤
          Fin.partialSum x l.castSucc := by
        simpa [cyclicBlockEvent, hpred, p] using hlocal
      exact (ih p hpLt hpU k hk hkp).trans hpl
  exact hmono b hb a ha hab

/-- The adjacent-block conditions imply every selected cyclic survival
event. The proof sums nonnegative complete blocks before the block
containing the requested time, as in Bauer--Godrèche--Luck,
Appendix A, equation (A.5). -/
private lemma forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent
    {n : ℕ} (x : Fin n → G) (u : Finset (Fin n))
    (hu : u.Nonempty) (hx : x ∈ cyclicBlockEvent u hu) :
    ∀ k ∈ u, x ∈ cyclicSurvivalEvent k := by
  let first := u.min' hu
  let last := u.max' hu
  have hfirstU : first ∈ u := u.min'_mem hu
  have hlastU : last ∈ u := u.max'_mem hu
  have hwrapPred : ¬ (precedingStarts u first.castSucc).Nonempty := by
    rintro ⟨p, hp⟩
    have hpU : p ∈ u := (Finset.mem_filter.mp hp).1
    have hpLt : p < first := (Finset.mem_filter.mp hp).2
    exact (not_lt_of_ge (u.min'_le p hpU)) hpLt
  have hwrapAtFirst := hx first.castSucc
  have hlastFirst : Fin.partialSum x last.castSucc ≤
      Fin.partialSum x (Fin.last n) +
        Fin.partialSum x first.castSucc := by
    simpa [cyclicBlockEvent, hwrapPred, first, last] using hwrapAtFirst
  have hfirstLast : Fin.partialSum x first.castSucc ≤
      Fin.partialSum x last.castSucc :=
    cyclicBlockEvent_selected_partialSum_mono x u hu hx
      hfirstU hlastU (u.min'_le_max' hu)
  have htotal : 0 ≤ Fin.partialSum x (Fin.last n) := by
    have hle : Fin.partialSum x first.castSucc ≤
        Fin.partialSum x (Fin.last n) + Fin.partialSum x first.castSucc :=
      hfirstLast.trans hlastFirst
    have hsub : 0 ≤
        (Fin.partialSum x (Fin.last n) + Fin.partialSum x first.castSucc) -
          Fin.partialSum x first.castSucc := sub_nonneg.mpr hle
    simpa using hsub
  intro k hk
  apply (mem_cyclicSurvivalEvent_iff_partialSum x k).mpr
  refine ⟨htotal, ?_, ?_⟩
  · intro t hkt
    by_cases hEq : t.val = k.val
    · have ht : t = k.castSucc := Fin.ext (by simpa using hEq)
      rw [ht]
    have hktStrict : k.val < t.val := by omega
    have hpred : (precedingStarts u t).Nonempty := by
      exact ⟨k, Finset.mem_filter.mpr ⟨hk, hktStrict⟩⟩
    let p := (precedingStarts u t).max' hpred
    have hpMem := (precedingStarts u t).max'_mem hpred
    have hpU : p ∈ u := (Finset.mem_filter.mp hpMem).1
    have hkp : k ≤ p :=
      (precedingStarts u t).le_max' k
        (Finset.mem_filter.mpr ⟨hk, hktStrict⟩)
    have hlocal := hx t
    have hpt : Fin.partialSum x p.castSucc ≤
        Fin.partialSum x t := by
      simpa [cyclicBlockEvent, hpred, p] using hlocal
    exact (cyclicBlockEvent_selected_partialSum_mono x u hu hx
      hk hpU hkp).trans hpt
  · intro t htk
    have hkLast : Fin.partialSum x k.castSucc ≤
        Fin.partialSum x last.castSucc :=
      cyclicBlockEvent_selected_partialSum_mono x u hu hx
        hk hlastU (u.le_max' k hk)
    by_cases hpred : (precedingStarts u t).Nonempty
    · let p := (precedingStarts u t).max' hpred
      have hpMem := (precedingStarts u t).max'_mem hpred
      have hpU : p ∈ u := (Finset.mem_filter.mp hpMem).1
      have hfirstP : Fin.partialSum x first.castSucc ≤
          Fin.partialSum x p.castSucc :=
        cyclicBlockEvent_selected_partialSum_mono x u hu hx
          hfirstU hpU (u.min'_le p hpU)
      have hlocal := hx t
      have hpt : Fin.partialSum x p.castSucc ≤
          Fin.partialSum x t := by
        simpa [cyclicBlockEvent, hpred, p] using hlocal
      have hfirstT : Fin.partialSum x first.castSucc ≤
          Fin.partialSum x t := hfirstP.trans hpt
      have hstartT : Fin.partialSum x (Fin.last n) +
          Fin.partialSum x first.castSucc ≤
            Fin.partialSum x (Fin.last n) + Fin.partialSum x t :=
        by
          simpa [add_comm] using
            add_le_add_right hfirstT (Fin.partialSum x (Fin.last n))
      exact hkLast.trans (hlastFirst.trans hstartT)
    · have hlocal := hx t
      have hlt : Fin.partialSum x last.castSucc ≤
          Fin.partialSum x (Fin.last n) +
            Fin.partialSum x t := by
        simpa [cyclicBlockEvent, hpred, last] using hlocal
      exact hkLast.trans hlt

/-- Bauer--Godrèche--Luck, Appendix A, equation (A.5), for any nonempty
finite set of selected cyclic starts: the intersection of the cyclic
survival events equals the adjacent-block event. -/
private lemma iInter_cyclicSurvivalEvent_eq_cyclicBlockEvent
    {n : ℕ} (u : Finset (Fin n)) (hu : u.Nonempty) :
    (⋂ k ∈ u, cyclicSurvivalEvent (G := G) k) =
      cyclicBlockEvent (G := G) u hu := by
  ext x
  simp only [Set.mem_iInter]
  constructor
  · exact mem_cyclicBlockEvent_of_forall_cyclicSurvivalEvent x u hu
  · exact forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent x u hu

variable [MeasurableSpace G] [MeasurableAdd₂ G]

/-- The adjacent-block event is measurable because it is a finite
intersection of measurable cyclic survival events. -/
private lemma measurableSet_cyclicBlockEvent
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    {n : ℕ} (u : Finset (Fin n)) (hu : u.Nonempty) :
    MeasurableSet (cyclicBlockEvent (G := G) u hu) := by
  rw [← iInter_cyclicSurvivalEvent_eq_cyclicBlockEvent (G := G) u hu]
  exact MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ =>
      measurableSet_cyclicSurvivalEvent hIci k

/-- Substituting the block decomposition (A.5) into the finite
inclusion--exclusion identity (A.4) of Bauer--Godrèche--Luck,
Appendix A. -/
private lemma measureReal_nonnegative_endpoint_eq_cyclicBlock_sum
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
private lemma cyclicBlockEvent_gapSurvival {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → G) (hx : x ∈ cyclicBlockEvent u hu)
    (j : Fin u.card) (t : Fin (cyclicGapLength u hu j + 1)) :
    0 ≤ Fin.partialSum (cyclicGapCoordinates hn u hu x j) t := by
  rw [partialSum_cyclicGapCoordinates hn u hu x j t]
  have hselected := forall_cyclicSurvivalEvent_of_mem_cyclicBlockEvent x u hu hx
    (u.orderEmbOfFin rfl j) (u.orderEmbOfFin_mem rfl j)
  exact hselected ⟨t.val, by
    have hbound := blockStart_add_cyclicGapLength_le u hu j
    omega⟩

omit [MeasurableSpace G] [MeasurableAdd₂ G] in
/-- If every adjacent cyclic block survives, the original prefix path
satisfies the adjacent-block inequalities of (A.5). -/
private lemma cyclicBlockEvent_of_gapSurvival {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty)
    (x : Fin n → G)
    (hx : ∀ j : Fin u.card,
      ∀ t : Fin (cyclicGapLength u hu j + 1),
        0 ≤ Fin.partialSum (cyclicGapCoordinates hn u hu x j) t) :
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
    rw [partialSum_cyclicGapCoordinates hn u hu x j d, hj] at hlocal
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
    rw [partialSum_cyclicGapCoordinates hn u hu x last d] at hlocal
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
private lemma cyclicBlockEvent_eq_gapSurvival {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    cyclicBlockEvent u hu =
      {x : Fin n → G | ∀ j : Fin u.card,
        ∀ t : Fin (cyclicGapLength u hu j + 1),
          0 ≤ Fin.partialSum (cyclicGapCoordinates hn u hu x j) t} := by
  ext x
  constructor
  · intro hx j t
    exact cyclicBlockEvent_gapSurvival hn u hu x hx j t
  · intro hx
    exact cyclicBlockEvent_of_gapSurvival hn u hu x hx

omit [IsOrderedAddMonoid G] in
private lemma measurableSet_nonnegativePartialSum (m : ℕ)
    (hIci : MeasurableSet (Set.Ici (0 : G))) :
    MeasurableSet {z : Fin m → G |
      ∀ t : Fin (m + 1), 0 ≤ Fin.partialSum z t} := by
  have hpartial (t : Fin (m + 1)) :
      Measurable (fun z : Fin m → G => Fin.partialSum z t) := by
    induction t using Fin.induction with
    | zero => simp
    | succ t ih =>
        have heq :
            (fun z : Fin m → G => Fin.partialSum z t.succ) =
              fun z => Fin.partialSum z t.castSucc + z t := by
          funext z
          exact Fin.partialSum_succ z t
        rw [heq]
        exact ih.add (measurable_pi_apply t)
  have h : MeasurableSet (⋂ t : Fin (m + 1),
      {z : Fin m → G | 0 ≤ Fin.partialSum z t}) :=
    MeasurableSet.iInter fun t =>
      hIci.preimage (hpartial t)
  simpa only [Set.iInter_ofPred] using h

/-- Bauer--Godrèche--Luck, Appendix A, equation (A.6): the selected cyclic
survival intersection factors into the survival probabilities of its
disjoint cyclic blocks under an IID finite product law. -/
private lemma measure_pi_cyclicBlockEvent_eq_prod
    (hIci : MeasurableSet (Set.Ici (0 : G)))
    (ν : Measure G) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n)
    (u : Finset (Fin n)) (hu : u.Nonempty) :
    Measure.pi (fun _ : Fin n => ν) (cyclicBlockEvent u hu) =
      ∏ j : Fin u.card,
        Measure.pi (fun _ : Fin (cyclicGapLength u hu j) => ν)
          {z : Fin (cyclicGapLength u hu j) → G |
            ∀ t : Fin (cyclicGapLength u hu j + 1),
              0 ≤ Fin.partialSum z t} := by
  let length : ℕ → ℕ :=
    cyclicGapLengthAt u hu
  let event : ∀ j : Fin u.card, Set (Fin (length j.val) → G) :=
    fun j => {z | ∀ t : Fin (length j.val + 1), 0 ≤ Fin.partialSum z t}
  have hmeas (j : Fin u.card) : MeasurableSet (event j) :=
    measurableSet_nonnegativePartialSum (length j.val) hIci
  have htotal : AdditivePath.blockStart length u.card = n :=
    blockStart_cyclicGapLength_card u hu
  have hproduct := measure_pi_forall_variableConsecutiveBlockEvent_of_sum
    ν length u.card n htotal event hmeas
  let e := Fin.cyclicCoordinateReindex hn
    (u.orderEmbOfFin rfl ⟨0, Finset.card_pos.mpr hu⟩)
  let T : (Fin n → G) ≃ᵐ (Fin n → G) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => G) e.symm
  have hmap : (Measure.pi (fun _ : Fin n => ν)).map T =
      Measure.pi (fun _ : Fin n => ν) := by
    simpa [T] using Measure.pi_map_piCongrLeft e.symm
      (fun _ : Fin n => ν)
  have hT (x : Fin n → G) (i : Fin n) : T x i = x (e i) := by
    simpa [T, MeasurableEquiv.coe_piCongrLeft] using
      (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => G)
        e.symm x (e i))
  let blockEvent : Set (Fin n → G) :=
    {y | ∀ j : Fin u.card,
      (fun i : Fin (length j.val) =>
        y ⟨AdditivePath.blockStart length j.val + i.val, by
          have hbound := blockStart_add_cyclicGapLength_le u hu j
          have hi : i.val < cyclicGapLength u hu j := by
            exact i.isLt
          change AdditivePath.blockStart length j.val +
            cyclicGapLength u hu j ≤ n at hbound
          omega⟩) ∈ event j}
  have hevent : cyclicBlockEvent u hu = T ⁻¹' blockEvent := by
    rw [cyclicBlockEvent_eq_gapSurvival hn u hu]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, blockEvent]
    apply forall_congr'
    intro j
    have hvec :
        cyclicGapCoordinates hn u hu x j =
          (fun i : Fin (cyclicGapLength u hu j) =>
            T x ⟨AdditivePath.blockStart length j.val + i.val, by
              have hbound := blockStart_add_cyclicGapLength_le u hu j
              change AdditivePath.blockStart length j.val +
                cyclicGapLength u hu j ≤ n at hbound
              omega⟩) := by
      funext i
      exact (hT x _).symm
    rcases j with ⟨j, hj⟩
    simp only [event, length, hvec]
    rfl
  have hblockMeas : MeasurableSet blockEvent := by
    have heq : blockEvent = T.symm ⁻¹' cyclicBlockEvent u hu := by
      rw [hevent]
      ext y
      simp
    rw [heq]
    exact (measurableSet_cyclicBlockEvent hIci u hu).preimage T.symm.measurable
  rw [hevent, ← Measure.map_apply T.measurable hblockMeas, hmap]
  change (Measure.pi (fun _ : Fin n => ν)) blockEvent = _
  calc
    (Measure.pi (fun _ : Fin n => ν)) blockEvent =
        ∏ j : Fin u.card,
          Measure.pi (fun _ : Fin (length j.val) => ν) (event j) := by
      simpa only [blockEvent] using hproduct
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      rfl

end ProbabilityTheory.RandomWalk

end
