/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.LadderTime

/-!
# Descending records and nonnegative survival

The public definitions and theorems in this file are:

- ProbabilityTheory.RandomWalk.IsStrictDescendingRecord:
  $S_j<\min_{0\le i<j}S_i$ at a positive time $j$.
- ProbabilityTheory.RandomWalk.strictDescendingLocalTime:
  the number of strict descending records through time $n$.
- ProbabilityTheory.RandomWalk.strictDescendingLadderTime:
  the first time at which the descending record count reaches $k$.
- ProbabilityTheory.RandomWalk.strictDescendingLocalTime_mono:
  $n\le m$ implies $\ell_n^-\le\ell_m^-$.
- ProbabilityTheory.RandomWalk.strictDescendingLocalTime_measurable:
  the finite strict-descending record count is measurable.
- ProbabilityTheory.RandomWalk.strictDescendingLadderTime_le_iff_localTime_ge:
  $T_k^-\le n$ if and only if $k\le\ell_n^-$.
- ProbabilityTheory.RandomWalk.measurableSet_strictDescendingLadderTime_le:
  the finite-horizon descending ladder-time event is measurable.
- ProbabilityTheory.RandomWalk.strictDescendingLadderTime_measurable:
  the extended-natural-valued descending ladder time is measurable.
- ProbabilityTheory.RandomWalk.survivesNonnegative_iff_strictDescendingLocalTime_eq_zero:
  $S_j\ge0$ for $1\le j\le n$ if and only if the descending record
  count through $n$ is zero.
- ProbabilityTheory.RandomWalk.survivesNonnegative_iff_firstDescendingLadderTime_gt:
  $C_n=\{T^-_1>n\}$.
- ProbabilityTheory.RandomWalk.measure_survival_eq_firstDescendingLadderTime_gt:
  $\mathbb P(C_n)=\mathbb P(T^-_1>n)$ for any measure on increment paths.

The descending ladder-time interpretation of survival is used in
Francesco Caravenna and Loïc Chaumont, *Invariance principles for random
walks conditioned to stay positive*, Lemma 2.1, DOI 10.1214/07-AIHP119.
The strict local-time construction follows Chaumont--Doney,
*Invariance principles for local times at the maximum of random walks and
Lévy processes*, Section 2, DOI 10.1214/09-AOP512, applied to the
reflected increment sequence.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

attribute [local instance] Classical.propDecidable

/-- A strict new minimum at a positive time. -/
def IsStrictDescendingRecord (increment : ℕ → ℝ) (j : ℕ) : Prop :=
  0 < j ∧ ∀ i < j,
    AdditivePath.displacement j increment <
      AdditivePath.displacement i increment

/-- New minima of a walk are new maxima of its negation. -/
theorem isStrictDescendingRecord_iff_ascending_neg
    (increment : ℕ → ℝ) (j : ℕ) :
    IsStrictDescendingRecord increment j ↔
      IsStrictAscendingRecord (fun i => -increment i) j := by
  simp [IsStrictDescendingRecord, IsStrictAscendingRecord,
    AdditivePath.displacement_neg]

/-- Number of strict descending records through time n. -/
noncomputable def strictDescendingLocalTime
    (increment : ℕ → ℝ) (n : ℕ) : ℕ :=
  strictAscendingLocalTime (fun i => -increment i) n

/-- The descending record count is the number of strict new minima. -/
theorem strictDescendingLocalTime_eq_card
    (increment : ℕ → ℝ) (n : ℕ) :
    strictDescendingLocalTime increment n =
      ((Finset.Icc 1 n).filter (IsStrictDescendingRecord increment)).card := by
  unfold strictDescendingLocalTime strictAscendingLocalTime
  congr 1
  ext j
  simp [isStrictDescendingRecord_iff_ascending_neg]

/-- The first time at which the reflected walk has accumulated k strict
ascending records. -/
noncomputable def strictDescendingLadderTime
    (increment : ℕ → ℝ) (k : ℕ) : WithTop ℕ :=
  strictAscendingLadderTime (fun i => -increment i) k

/-- The number of strict new minima is nondecreasing. -/
theorem strictDescendingLocalTime_mono
    (increment : ℕ → ℝ) {n m : ℕ} (hnm : n ≤ m) :
    strictDescendingLocalTime increment n ≤
      strictDescendingLocalTime increment m :=
  strictAscendingLocalTime_mono (fun i => -increment i) hnm

/-- The strict descending record count is measurable at every finite
horizon. -/
theorem strictDescendingLocalTime_measurable (n : ℕ) :
    Measurable (fun increment : ℕ → ℝ =>
      strictDescendingLocalTime increment n) := by
  have hneg : Measurable (fun increment : ℕ → ℝ =>
      fun i => -increment i) := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).neg
  exact (strictAscendingLocalTime_measurable n).comp hneg

/-- The k-th strict descending ladder time has occurred by n exactly
when the descending record count has reached k. -/
theorem strictDescendingLadderTime_le_iff_localTime_ge
    (increment : ℕ → ℝ) (k n : ℕ) :
    strictDescendingLadderTime increment k ≤ n ↔
      k ≤ strictDescendingLocalTime increment n :=
  strictAscendingLadderTime_le_iff_localTime_ge
    (fun i => -increment i) k n

/-- The finite-horizon descending ladder-time event is measurable. -/
theorem measurableSet_strictDescendingLadderTime_le (k n : ℕ) :
    MeasurableSet
      {increment : ℕ → ℝ |
        strictDescendingLadderTime increment k ≤ (n : WithTop ℕ)} := by
  have hset :
      {increment : ℕ → ℝ |
        strictDescendingLadderTime increment k ≤ (n : WithTop ℕ)} =
      {increment : ℕ → ℝ | k ≤ strictDescendingLocalTime increment n} := by
    ext increment
    exact strictDescendingLadderTime_le_iff_localTime_ge increment k n
  rw [hset]
  exact measurableSet_le measurable_const
    (strictDescendingLocalTime_measurable n)

/-- The strict descending ladder time is a measurable extended-natural-
valued random variable. -/
theorem strictDescendingLadderTime_measurable (k : ℕ) :
    Measurable (fun increment : ℕ → ℝ =>
      strictDescendingLadderTime increment k) := by
  have hneg : Measurable (fun increment : ℕ → ℝ =>
      fun i => -increment i) := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply i).neg
  exact (strictAscendingLadderTime_measurable k).comp hneg

/-- Nonnegative survival is equivalent to having no strict new minimum. -/
theorem survivesNonnegative_iff_strictDescendingLocalTime_eq_zero
    (increment : ℕ → ℝ) (n : ℕ) :
    SurvivesNonnegative n increment ↔
      strictDescendingLocalTime increment n = 0 := by
  rw [strictDescendingLocalTime_eq_card,
    Finset.card_filter_eq_zero_iff]
  constructor
  · intro hsurv j hj hrecord
    have hjle : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hjnonneg : 0 ≤ AdditivePath.displacement j increment :=
      hsurv.displacement_nonneg hjle
    have hjneg : AdditivePath.displacement j increment < 0 := by
      simpa [AdditivePath.displacement_zero] using
        hrecord.2 0 hrecord.1
    exact (not_lt_of_ge hjnonneg) hjneg
  · intro hno
    have hnonnegative :
        ∀ j : ℕ, j ≤ n →
          0 ≤ AdditivePath.displacement j increment := by
      intro j
      induction j using Nat.strong_induction_on with
      | h j ih =>
          intro hj
          by_cases hjzero : j = 0
          · subst j
            simp [AdditivePath.displacement_zero]
          · by_contra hge
            have hjneg : AdditivePath.displacement j increment < 0 :=
              lt_of_not_ge hge
            have hjpositive : 0 < j := Nat.pos_of_ne_zero hjzero
            have hrecord : IsStrictDescendingRecord increment j := by
              refine ⟨hjpositive, ?_⟩
              intro i hi
              exact hjneg.trans_le
                (ih i hi (Nat.le_trans (Nat.le_of_lt hi) hj))
            exact hno j (Finset.mem_Icc.mpr ⟨hjpositive, hj⟩) hrecord
    intro j
    exact hnonnegative (j + 1) (Nat.succ_le_of_lt j.isLt)

/-- Survival through time n means that the first strict descending ladder
time is greater than n. This is the event identity used in
Caravenna--Chaumont, Lemma 2.1. -/
theorem survivesNonnegative_iff_firstDescendingLadderTime_gt
    (increment : ℕ → ℝ) (n : ℕ) :
    SurvivesNonnegative n increment ↔
      (n : WithTop ℕ) < strictDescendingLadderTime increment 1 := by
  rw [survivesNonnegative_iff_strictDescendingLocalTime_eq_zero]
  constructor
  · intro hzero
    unfold strictDescendingLadderTime strictAscendingLadderTime
    apply lt_sInf_iff.mpr
    refine ⟨(n + 1 : ℕ), by exact_mod_cast Nat.lt_succ_self n, ?_⟩
    rintro t ⟨m, rfl, hm⟩
    have hnm : n < m := by
      by_contra hnot
      have hmn : m ≤ n := Nat.le_of_not_gt hnot
      have hmncount :=
        strictDescendingLocalTime_mono increment hmn
      change strictDescendingLocalTime increment m ≥ 1 at hm
      omega
    exact_mod_cast Nat.succ_le_of_lt hnm
  · intro htime
    by_contra hnonzero
    have hpositive : 1 ≤ strictDescendingLocalTime increment n :=
      Nat.one_le_iff_ne_zero.mpr hnonzero
    have hle : strictDescendingLadderTime increment 1 ≤ n :=
      strictAscendingLadderTime_le_of_localTime_ge
        (fun i => -increment i) hpositive
    exact (not_lt_of_ge hle) htime

/-- The first descending ladder-time tail event is measurable. -/
theorem measurableSet_firstDescendingLadderTime_gt (n : ℕ) :
    MeasurableSet
      {increment : ℕ → ℝ |
        (n : WithTop ℕ) < strictDescendingLadderTime increment 1} := by
  convert measurableSet_survivesNonnegative n using 1
  ext increment
  exact (survivesNonnegative_iff_firstDescendingLadderTime_gt
    increment n).symm

/-- The survival probability is the first descending ladder-time tail,
as in Caravenna--Chaumont, Lemma 2.1. -/
theorem measure_survival_eq_firstDescendingLadderTime_gt
    (μ : MeasureTheory.Measure (ℕ → ℝ)) (n : ℕ) :
    μ {increment | SurvivesNonnegative n increment} =
      μ {increment |
        (n : WithTop ℕ) < strictDescendingLadderTime increment 1} := by
  congr 1
  ext increment
  exact survivesNonnegative_iff_firstDescendingLadderTime_gt increment n

end ProbabilityTheory.RandomWalk

end
