/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.LadderTime
public import Probability.Process.RandomWalk.Path.Filtration

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
- ProbabilityTheory.RandomWalk.IsFirstSurvivingWindow.strictDescendingRecord:
  the first surviving length-$n$ window begins at a strict descending
  record whenever its starting time is positive.
- ProbabilityTheory.RandomWalk.IsCandidateWindowStart:
  a descending record whose earlier completed windows failed.
- ProbabilityTheory.RandomWalk.isFirstSurvivingWindow_iff_candidate_and_survives:
  the first surviving window is a candidate start followed by a surviving
  length-$n$ block.
- ProbabilityTheory.RandomWalk.measurableSet_isCandidateWindowStart_prefix:
  the candidate event is measurable from increments before its start.

The descending ladder-time interpretation of survival is used in
Francesco Caravenna and Loïc Chaumont, *Invariance principles for random
walks conditioned to stay positive*, Lemma 2.1, DOI 10.1214/07-AIHP119.
The strict local-time construction follows Chaumont--Doney,
*Invariance principles for local times at the maximum of random walks and
Lévy processes*, Section 2, DOI 10.1214/09-AOP512, applied to the
reflected increment sequence.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

attribute [local instance] Classical.propDecidable

/-- A strict new minimum at a positive time. -/
def IsStrictDescendingRecord (increment : ℕ → ℝ) (j : ℕ) : Prop :=
  0 < j ∧ ∀ i < j,
    AdditivePath.displacement j increment <
      AdditivePath.displacement i increment

/-- The first surviving length-`n` window begins at a strict descending
record when its start is positive. This is the record-time property behind
the first-window construction in Erwin Bolthausen, *On a functional central
limit theorem for random walks conditioned to stay positive*, Ann. Probab.
4(3) (1976), 480–485, DOI 10.1214/aop/1176996098; see also Vladislav
Vysotsky, *Positivity of integrated random walks*, Section 3.1, equation
(17), DOI 10.1214/12-AIHP487. -/
theorem IsFirstSurvivingWindow.strictDescendingRecord
    {n start : ℕ} {increment : ℕ → ℝ}
    (hfirst : IsFirstSurvivingWindow n start increment)
    (hpositive : 0 < start) :
    IsStrictDescendingRecord increment start := by
  refine ⟨hpositive, ?_⟩
  intro i hi
  by_contra hlt
  have hile : AdditivePath.displacement i increment ≤
      AdditivePath.displacement start increment := le_of_not_gt hlt
  obtain ⟨j, hj, hmin⟩ :=
    (Finset.range start).exists_min_image
      (fun t => AdditivePath.displacement t increment)
      ⟨i, Finset.mem_range.mpr hi⟩
  have hjlt : j < start := Finset.mem_range.mp hj
  have hjle : AdditivePath.displacement j increment ≤
      AdditivePath.displacement start increment :=
    (hmin i (Finset.mem_range.mpr hi)).trans hile
  have hwindow : SurvivesNonnegative n
      (fun k => increment (j + k)) := by
    apply (SurvivesNonnegative.shift_iff n j increment).2
    intro k
    let t := j + (k : ℕ) + 1
    by_cases ht : t < start
    · simpa [t, Nat.add_assoc] using hmin t (Finset.mem_range.mpr ht)
    · have htle : t ≤ start + n := by
        dsimp [t]
        omega
      by_cases heq : t = start
      · have hgoal : j + ((k : ℕ) + 1) = start := by
          simpa [t, Nat.add_assoc] using heq
        simpa [hgoal] using hjle
      · have hindex : t - start - 1 < n := by omega
        have hsurvive :=
          (SurvivesNonnegative.shift_iff n start increment).1 hfirst.1
            ⟨t - start - 1, hindex⟩
        have hposition : start + ((t - start - 1) + 1) = t := by omega
        rw [hposition] at hsurvive
        exact hjle.trans hsurvive
  exact hfirst.2 ⟨j, hjlt⟩ hwindow

/-- A candidate start for the first surviving length-`n` window is either
time zero or a strict descending record, and every earlier window ending
strictly before this start has failed. All these conditions concern the
prefix through `start`. -/
def IsCandidateWindowStart (n start : ℕ) (increment : ℕ → ℝ) : Prop :=
  (start = 0 ∨ IsStrictDescendingRecord increment start) ∧
    ∀ j : Fin start, (j : ℕ) + n < start →
      ¬ SurvivesNonnegative n (fun k => increment (j + k))

/-- The first-window event factors into a prefix candidate event and a
surviving future block. The strict record at `start` forces every earlier
window that overlaps `start` to fail. This is the finite-path decomposition
behind Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480–485,
DOI 10.1214/aop/1176996098. -/
theorem isFirstSurvivingWindow_iff_candidate_and_survives
    (n start : ℕ) (increment : ℕ → ℝ) :
    IsFirstSurvivingWindow n start increment ↔
      IsCandidateWindowStart n start increment ∧
        SurvivesNonnegative n (fun k => increment (start + k)) := by
  constructor
  · intro hfirst
    refine ⟨⟨?_, fun j _ => hfirst.2 j⟩, hfirst.1⟩
    by_cases hzero : start = 0
    · exact Or.inl hzero
    · exact Or.inr (hfirst.strictDescendingRecord (Nat.pos_of_ne_zero hzero))
  · rintro ⟨⟨hrecord, hfailed⟩, hsurvive⟩
    refine ⟨hsurvive, ?_⟩
    intro j
    by_cases hend : (j : ℕ) + n < start
    · exact hfailed j hend
    · intro hwindow
      rcases hrecord with hzero | hrecord
      · omega
      · have hjindex : start - (j : ℕ) - 1 < n := by omega
        have hjposition :=
          (SurvivesNonnegative.shift_iff n j increment).1 hwindow
            ⟨start - (j : ℕ) - 1, hjindex⟩
        have hendpoint : (j : ℕ) +
            ((start - (j : ℕ) - 1) + 1) = start := by omega
        rw [hendpoint] at hjposition
        exact (not_le_of_gt (hrecord.2 j j.isLt)) hjposition

/-- A shifted survival event is measurable from any prefix containing all
of its increment coordinates. -/
private theorem measurableSet_survivesNonnegative_shift_prefix
    (n j start : ℕ) (hbound : j + n ≤ start) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) start]
      {increment : ℕ → ℝ |
        SurvivesNonnegative n (fun k => increment (j + k))} := by
  rw [show {increment : ℕ → ℝ |
        SurvivesNonnegative n (fun k => increment (j + k))} =
      ⋂ k : Fin n,
        {increment | 0 ≤ AdditivePath.displacement (k + 1)
          (fun t => increment (j + t))} by
    ext increment
    simp [SurvivesNonnegative]]
  exact MeasurableSet.iInter fun k =>
    measurableSet_Ici.preimage
      (displacement_natAdd_measurable_prefix (E := ℝ)
        j (k + 1) start (by omega))

/-- The strict record event at `start` is measurable from the first
`start` increments. -/
private theorem measurableSet_strictDescendingRecord_prefix (start : ℕ) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) start]
      {increment : ℕ → ℝ | IsStrictDescendingRecord increment start} := by
  by_cases hs : 0 < start
  · rw [show {increment : ℕ → ℝ |
          IsStrictDescendingRecord increment start} =
        ⋂ i : Fin start,
          {increment | AdditivePath.displacement start increment <
            AdditivePath.displacement i increment} by
      ext increment
      simp [IsStrictDescendingRecord, hs, Fin.forall_iff]]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt
        (displacement_measurable_prefix (E := ℝ) le_rfl)
        (displacement_measurable_prefix (E := ℝ) i.isLt.le)
  · have hzero : start = 0 := by omega
    simp [IsStrictDescendingRecord, hzero]

/-- A candidate first-window start depends only on the increment prefix
through that start, so it can be multiplied by an independent future-block
event under an IID increment law. -/
theorem measurableSet_isCandidateWindowStart_prefix (n start : ℕ) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) start]
      {increment : ℕ → ℝ |
        IsCandidateWindowStart n start increment} := by
  rw [show {increment : ℕ → ℝ |
        IsCandidateWindowStart n start increment} =
      {increment | start = 0 ∨ IsStrictDescendingRecord increment start} ∩
        ⋂ j : Fin start,
          {increment | (j : ℕ) + n < start →
            ¬ SurvivesNonnegative n (fun k => increment (j + k))} by
    ext increment
    simp [IsCandidateWindowStart]]
  apply MeasurableSet.inter
  · by_cases hzero : start = 0
    · simp [hzero]
    · simpa [hzero] using measurableSet_strictDescendingRecord_prefix start
  · apply MeasurableSet.iInter
    intro j
    by_cases hj : (j : ℕ) + n < start
    · rw [show {increment : ℕ → ℝ |
            (j : ℕ) + n < start →
              ¬ SurvivesNonnegative n (fun k => increment (j + k))} =
          {increment | SurvivesNonnegative n
            (fun k => increment (j + k))}ᶜ by
        ext increment
        simp [hj]]
      exact (measurableSet_survivesNonnegative_shift_prefix
        n j start (by omega)).compl
    · simp [hj]

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
