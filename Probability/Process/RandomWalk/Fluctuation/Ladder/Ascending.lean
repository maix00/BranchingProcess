/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.Ladder.RecordLocalTime
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
# Strict ascending ladder times and heights

Let $(\xi_i)_{i\geq1}$ be increments, $S_0=0$, and
$S_n=\sum_{i=1}^n\xi_i$. Write
$\ell_n=\#\{1\leq j\leq n:S_j>\max_{0\leq i<j}S_i\}$ and define
$T_k=\inf\{n:\ell_n\geq k\}$, with $T_k=\infty$ if the set is empty.
Set $H_k=S_{T_k}$ when $T_k<\infty$ and $H_k=\infty$ otherwise. The
public definitions and theorems in this file are:

- ProbabilityTheory.RandomWalk.strictAscendingLadderTime:
  $T_k=\inf\{n\ge0:\ell_n\ge k\}$, with $T_k=\infty$ if the set is empty.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_zero:
  $T_0=0$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_mono:
  $k\le l$ implies $T_k\le T_l$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_le_of_localTime_ge:
  $k\le\ell_n$ implies $T_k\le n$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_le_iff_localTime_ge:
  $T_k\le n$ if and only if $k\le\ell_n$.
- ProbabilityTheory.RandomWalk.measurableSet_strictAscendingLadderTime_le:
  the finite-horizon ladder-time event $\{T_k\le n\}$ is measurable.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_measurable:
  the extended-natural-valued ladder time is measurable.
- ProbabilityTheory.RandomWalk.strictAscendingLadderTime_eq_top_of_localTime_lt:
  if $\ell_n<k$ for every $n$, then $T_k=\infty$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderHeight:
  $H_k=S_{T_k}$ when $T_k<\infty$, and $H_k=\infty$ otherwise.
- ProbabilityTheory.RandomWalk.strictAscendingLadderHeight_zero:
  $H_0=0$.
- ProbabilityTheory.RandomWalk.isStrictAscendingRecord_of_ladderTime_eq:
  if $k>0$ and $T_k=n<\infty$, then $n$ is a strict ascending record.
- ProbabilityTheory.RandomWalk.strictAscendingLadderHeight_nonneg:
  $H_k\ge0$ in $\mathbb R\cup\{\infty\}$.
- ProbabilityTheory.RandomWalk.strictAscendingLadderHeight_mono:
  $k\le l$ implies $H_k\le H_l$.
- ProbabilityTheory.RandomWalk.measurableSet_strictAscendingLadderHeight_le:
  the event $\{H_k\le x\}$ is measurable.
- ProbabilityTheory.RandomWalk.strictAscendingLadderHeight_measurable:
  $H_k:\mathbb R^{\mathbb N}\to\mathbb R\cup\{\infty\}$ is measurable.

These objects are the strict ascending ladder time and height in Section 2,
after equation (2.2), of Loïc Chaumont and R. A. Doney, *Invariance
principles for local times at the maximum of random walks and Lévy
processes*, Ann. Probab. 38(4) (2010), 1368--1389, DOI 10.1214/09-AOP512.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The first time at which the discrete local time at the maximum
reaches level k. The infimum of the empty set is infinity. -/
noncomputable def strictAscendingLadderTime
    (increment : ℕ → ℝ) (k : ℕ) : WithTop ℕ :=
  sInf {t : WithTop ℕ |
    ∃ n : ℕ, t = n ∧ k ≤ strictAscendingLocalTime increment n}

/-- The zeroth strict ascending ladder time is the initial time. -/
theorem strictAscendingLadderTime_zero (increment : ℕ → ℝ) :
    strictAscendingLadderTime increment 0 = 0 := by
  apply le_antisymm
  · apply sInf_le
    exact ⟨0, rfl, Nat.zero_le _⟩
  · exact bot_le

/-- Reaching a higher record count cannot occur earlier. -/
theorem strictAscendingLadderTime_mono
    (increment : ℕ → ℝ) {k l : ℕ} (hkl : k ≤ l) :
    strictAscendingLadderTime increment k ≤
      strictAscendingLadderTime increment l := by
  unfold strictAscendingLadderTime
  apply sInf_le_sInf
  rintro t ⟨n, rfl, hn⟩
  exact ⟨n, rfl, hkl.trans hn⟩

/-- A record level reached by time n has ladder time at most n. -/
theorem strictAscendingLadderTime_le_of_localTime_ge
    (increment : ℕ → ℝ) {k n : ℕ}
    (hkn : k ≤ strictAscendingLocalTime increment n) :
    strictAscendingLadderTime increment k ≤ n := by
  unfold strictAscendingLadderTime
  exact sInf_le ⟨n, rfl, hkn⟩

/-- The k-th ascending ladder time has occurred by n exactly when the
record local time has reached k by n. -/
theorem strictAscendingLadderTime_le_iff_localTime_ge
    (increment : ℕ → ℝ) (k n : ℕ) :
    strictAscendingLadderTime increment k ≤ n ↔
      k ≤ strictAscendingLocalTime increment n := by
  constructor
  · intro htime
    by_contra hnot
    have hlocal : strictAscendingLocalTime increment n < k :=
      Nat.lt_of_not_ge hnot
    have hstrict : (n : WithTop ℕ) <
        strictAscendingLadderTime increment k := by
      unfold strictAscendingLadderTime
      apply lt_sInf_iff.mpr
      refine ⟨(n + 1 : ℕ), by exact_mod_cast Nat.lt_succ_self n, ?_⟩
      rintro t ⟨m, rfl, hm⟩
      have hnm : n < m := by
        by_contra hnotLess
        have hmn : m ≤ n := Nat.le_of_not_gt hnotLess
        have hmono := strictAscendingLocalTime_mono increment hmn
        omega
      exact_mod_cast Nat.succ_le_of_lt hnm
    exact (not_lt_of_ge htime) hstrict
  · exact strictAscendingLadderTime_le_of_localTime_ge increment

/-- The event that a strict ascending ladder time has occurred by a
finite horizon is measurable. -/
theorem measurableSet_strictAscendingLadderTime_le (k n : ℕ) :
    MeasurableSet
      {increment : ℕ → ℝ |
        strictAscendingLadderTime increment k ≤ (n : WithTop ℕ)} := by
  have hset :
      {increment : ℕ → ℝ |
        strictAscendingLadderTime increment k ≤ (n : WithTop ℕ)} =
      {increment : ℕ → ℝ | k ≤ strictAscendingLocalTime increment n} := by
    ext increment
    exact strictAscendingLadderTime_le_iff_localTime_ge increment k n
  rw [hset]
  exact measurableSet_le measurable_const
    (strictAscendingLocalTime_measurable n)

/-- The strict ascending ladder time is a measurable extended-natural-
valued random variable. -/
theorem strictAscendingLadderTime_measurable (k : ℕ) :
    Measurable (fun increment : ℕ → ℝ =>
      strictAscendingLadderTime increment k) := by
  have hfinite (n : ℕ) : MeasurableSet
      ((fun increment : ℕ → ℝ => strictAscendingLadderTime increment k) ⁻¹'
        {(n : WithTop ℕ)}) := by
    have hlt : MeasurableSet
        {increment : ℕ → ℝ |
          strictAscendingLadderTime increment k < (n : WithTop ℕ)} := by
      cases n with
      | zero => simp
      | succ n =>
        have hset :
            {increment : ℕ → ℝ |
              strictAscendingLadderTime increment k < ((n + 1 : ℕ) : WithTop ℕ)} =
            {increment : ℕ → ℝ |
              strictAscendingLadderTime increment k ≤ (n : WithTop ℕ)} := by
          ext increment
          cases ht : strictAscendingLadderTime increment k with
          | top => simp [ht]
          | coe t =>
            simp only [Set.mem_ofPred_eq]
            rw [ht]
            calc
              (t : WithTop ℕ) < ((n + 1 : ℕ) : WithTop ℕ) ↔
                  t < n + 1 := WithTop.coe_lt_coe
              _ ↔ t ≤ n := Nat.lt_succ_iff
              _ ↔ (t : WithTop ℕ) ≤ (n : WithTop ℕ) :=
                WithTop.coe_le_coe.symm
        rw [hset]
        exact measurableSet_strictAscendingLadderTime_le k n
    have hset :
        (fun increment : ℕ → ℝ =>
          strictAscendingLadderTime increment k) ⁻¹'
            {(n : WithTop ℕ)} =
        {increment : ℕ → ℝ |
          strictAscendingLadderTime increment k ≤ (n : WithTop ℕ)} \
        {increment : ℕ → ℝ |
          strictAscendingLadderTime increment k < (n : WithTop ℕ)} := by
      ext increment
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
        Set.mem_ofPred_eq]
      exact eq_iff_le_not_lt
    rw [hset]
    exact (measurableSet_strictAscendingLadderTime_le k n).diff hlt
  apply measurable_to_countable'
  intro value
  cases value with
  | coe n => exact hfinite n
  | top =>
    have hset :
        (fun increment : ℕ → ℝ => strictAscendingLadderTime increment k) ⁻¹'
          {⊤} =
        (⋃ n : ℕ,
          (fun increment : ℕ → ℝ => strictAscendingLadderTime increment k) ⁻¹'
            {(n : WithTop ℕ)})ᶜ := by
      ext increment
      cases ht : strictAscendingLadderTime increment k with
      | top => simp [ht]
      | coe n => simp [ht]
    rw [hset]
    exact (MeasurableSet.iUnion hfinite).compl

/-- A record level never reached has infinite ladder time. -/
theorem strictAscendingLadderTime_eq_top_of_localTime_lt
    (increment : ℕ → ℝ) {k : ℕ}
    (hk : ∀ n, strictAscendingLocalTime increment n < k) :
    strictAscendingLadderTime increment k = ⊤ := by
  unfold strictAscendingLadderTime
  have hempty :
      {t : WithTop ℕ |
        ∃ n : ℕ, t = n ∧ k ≤ strictAscendingLocalTime increment n} =
        ∅ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨n, _, hn⟩
    exact (Nat.not_le.mpr (hk n)) hn
  rw [hempty, sInf_empty]

/-- The height at a strict ascending ladder time, with infinity when
that time is infinite. -/
noncomputable def strictAscendingLadderHeight
    (increment : ℕ → ℝ) (k : ℕ) : WithTop ℝ :=
  match strictAscendingLadderTime increment k with
  | none => ⊤
  | some n => ((AdditivePath.displacement n increment : ℝ) : WithTop ℝ)

/-- The zeroth ladder height is the initial position. -/
theorem strictAscendingLadderHeight_zero (increment : ℕ → ℝ) :
    strictAscendingLadderHeight increment 0 = 0 := by
  simp [strictAscendingLadderHeight, strictAscendingLadderTime_zero,
    AdditivePath.displacement_zero]

/-- A positive ladder level is first reached at a strict new maximum. -/
theorem isStrictAscendingRecord_of_ladderTime_eq
    (increment : ℕ → ℝ) {k n : ℕ} (hk : 0 < k)
    (htime : strictAscendingLadderTime increment k = (n : WithTop ℕ)) :
    IsStrictAscendingRecord increment n := by
  have hlocal : k ≤ strictAscendingLocalTime increment n :=
    (strictAscendingLadderTime_le_iff_localTime_ge increment k n).mp
      (by rw [htime])
  cases n with
  | zero =>
    simp [strictAscendingLocalTime_zero] at hlocal
    omega
  | succ n =>
    by_contra hnot
    have hsame := strictAscendingLocalTime_succ increment n
    simp [hnot] at hsame
    have hprev : k ≤ strictAscendingLocalTime increment n := by omega
    have htimePrev :=
      (strictAscendingLadderTime_le_iff_localTime_ge increment k n).mpr hprev
    rw [htime] at htimePrev
    exact (not_le_of_gt (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)))
      htimePrev

/-- Every finite strict ascending ladder height is nonnegative; an
infinite ladder time has height infinity. -/
theorem strictAscendingLadderHeight_nonneg
    (increment : ℕ → ℝ) (k : ℕ) :
    (0 : WithTop ℝ) ≤ strictAscendingLadderHeight increment k := by
  by_cases hk : k = 0
  · subst k
    simp [strictAscendingLadderHeight_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    cases ht : strictAscendingLadderTime increment k with
    | top => simp [strictAscendingLadderHeight, ht]
    | coe n =>
      have hrecord :=
        isStrictAscendingRecord_of_ladderTime_eq increment hkpos ht
      have hpositive : 0 < AdditivePath.displacement n increment := by
        simpa [AdditivePath.displacement_zero] using
          hrecord.2 0 hrecord.1
      simpa [strictAscendingLadderHeight, ht] using
        (WithTop.coe_le_coe.mpr hpositive.le)

/-- Successive strict ascending ladder heights are nondecreasing. -/
theorem strictAscendingLadderHeight_mono
    (increment : ℕ → ℝ) :
    Monotone (strictAscendingLadderHeight increment) := by
  intro k l hkl
  by_cases hlzero : l = 0
  · have hkzero : k = 0 := by omega
    simp [hkzero, hlzero]
  have hlpos : 0 < l := Nat.pos_of_ne_zero hlzero
  cases htl : strictAscendingLadderTime increment l with
  | top => simp [strictAscendingLadderHeight, htl]
  | coe n =>
    cases htk : strictAscendingLadderTime increment k with
    | top =>
      have htime := strictAscendingLadderTime_mono increment hkl
      rw [htk, htl] at htime
      exact False.elim ((not_le_of_gt (WithTop.coe_lt_top n)) htime)
    | coe m =>
      have htime := strictAscendingLadderTime_mono increment hkl
      rw [htk, htl] at htime
      have hmn : m ≤ n := WithTop.coe_le_coe.mp htime
      have hdisp : AdditivePath.displacement m increment ≤
          AdditivePath.displacement n increment := by
        by_cases hmeq : m = n
        · simp [hmeq]
        · have hmlt : m < n := lt_of_le_of_ne hmn hmeq
          exact (isStrictAscendingRecord_of_ladderTime_eq
            increment hlpos htl).2 m hmlt |>.le
      simpa [strictAscendingLadderHeight, htk, htl] using
        (WithTop.coe_le_coe.mpr hdisp)

/-- The finite-height event for an ascending ladder level is measurable.
It is a countable union over the finite possible ladder times. -/
theorem measurableSet_strictAscendingLadderHeight_le (k : ℕ) (x : ℝ) :
    MeasurableSet
      {increment : ℕ → ℝ |
        strictAscendingLadderHeight increment k ≤ (x : WithTop ℝ)} := by
  have hset :
      {increment : ℕ → ℝ |
        strictAscendingLadderHeight increment k ≤ (x : WithTop ℝ)} =
      ⋃ n : ℕ,
        {increment : ℕ → ℝ |
          strictAscendingLadderTime increment k = (n : WithTop ℕ) ∧
          AdditivePath.displacement n increment ≤ x} := by
    ext increment
    cases ht : strictAscendingLadderTime increment k with
    | top => simp [strictAscendingLadderHeight, ht]
    | coe n =>
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · intro hheight
        refine ⟨n, ht, ?_⟩
        simpa [strictAscendingLadderHeight, ht] using hheight
      · rintro ⟨j, hj, hdisp⟩
        have hjEq : j = n := by
          rw [ht] at hj
          exact WithTop.coe_inj.mp hj.symm
        subst j
        simpa [strictAscendingLadderHeight, ht] using hdisp
  rw [hset]
  apply MeasurableSet.iUnion
  intro n
  have htime : MeasurableSet
      {increment : ℕ → ℝ |
        strictAscendingLadderTime increment k = (n : WithTop ℕ)} := by
    change MeasurableSet
      ((fun increment : ℕ → ℝ => strictAscendingLadderTime increment k) ⁻¹'
        {(n : WithTop ℕ)})
    exact (strictAscendingLadderTime_measurable k)
      (measurableSet_singleton _)
  exact htime.inter
    (measurableSet_le (displacement_measurable n) measurable_const)

/-- The extended-real ascending ladder height is measurable. The finite
sublevel events determine the Borel σ-algebra of `WithTop ℝ`. -/
theorem strictAscendingLadderHeight_measurable (k : ℕ) :
    Measurable (fun increment : ℕ → ℝ =>
      strictAscendingLadderHeight increment k) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simp
  | coe y =>
    exact measurableSet_strictAscendingLadderHeight_le k y

end ProbabilityTheory.RandomWalk

end
