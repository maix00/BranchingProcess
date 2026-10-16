/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Interpolation.Basic
public import Combinatorics.Sequence.Block
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Nonnegative finite random-walk paths

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.SurvivesNonnegative`: the event
  $C_n=\{S_j\ge0:1\le j\le n\}$.
- `ProbabilityTheory.RandomWalk.measurableSet_survivesNonnegative`: $C_n$ is measurable.
- `ProbabilityTheory.RandomWalk.SurvivesNonnegative.mono`: $C_m\subseteq C_n$
  whenever $n\le m$.
- `ProbabilityTheory.RandomWalk.SurvivesNonnegative.displacement_nonneg`:
  $C_n$ also gives $S_k\ge0$ for $0\le k\le n$.
- `ProbabilityTheory.RandomWalk.SurvivesNonnegative.normalizedLinearCadlagPathIcc_nonnegative`:
  $C_n$ gives $S^{\mathrm{lin}}_n(t)\ge0$ for every $t\in[0,1]$
  whenever the normalization scale is positive.
- `ProbabilityTheory.RandomWalk.SurvivesNonnegative.shift_iff`:
  a shifted window survives precisely when $S_{m+j}\ge S_m$ throughout
  that window.
- `ProbabilityTheory.RandomWalk.IsFirstSurvivingWindow`: the first
  length-$n$ surviving window starts at a specified time $m$.
- `ProbabilityTheory.RandomWalk.FiniteSurvivesNonnegative`: the same
  survival condition on a finite vector of $n$ increments.
- `ProbabilityTheory.RandomWalk.finiteSurvivesNonnegative_blockCoordinates_iff`:
  survival of a shifted infinite sequence is equivalent to survival of
  its finite coordinate block.
- `ProbabilityTheory.RandomWalk.measurableSet_finiteSurvivesNonnegative`:
  the finite survival block event is measurable.
- `ProbabilityTheory.RandomWalk.measurableSet_isFirstSurvivingWindow`:
  this finite-time first-window event is measurable.
- `ProbabilityTheory.RandomWalk.IsFirstSurvivingWindow.unique`:
  the first surviving window has a unique starting time.
- `ProbabilityTheory.RandomWalk.exists_firstSurvivingWindow_le`:
  any surviving window has a first predecessor no later than itself.
- `ProbabilityTheory.RandomWalk.SurvivesNonnegative.normalizedStepCadlagPathIcc_nonnegative`:
  for a positive normalization, $C_n$ gives a nonnegative normalized
  càdlàg path at every $t\in[0,1]$.

The event $C_n$ is the survival event used by Francesco Caravenna and
Loïc Chaumont, *Invariance principles for random walks conditioned to stay
positive*, Ann. Inst. H. Poincaré Probab. Stat. 44(1) (2008), 170–190,
Lemma 2.1 and equation (3.3), DOI 10.1214/07-AIHP119.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- The partial sums through time `n` are nonnegative at positive integer
times. This is the survival event in Caravenna--Chaumont, Lemma 2.1. -/
def SurvivesNonnegative (n : ℕ) (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n, 0 ≤ AdditivePath.displacement (k + 1) increment

/-- Survival of all positive-time prefix sums of a finite increment block. -/
def FiniteSurvivesNonnegative {n : ℕ} (block : Fin n → ℝ) : Prop :=
  ∀ k : Fin n,
    0 ≤ ∑ j : Fin (k + 1),
      block ⟨j, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩

/-- The finite block records exactly the survival event of the shifted
infinite increment sequence. -/
theorem finiteSurvivesNonnegative_blockCoordinates_iff
    (n start : ℕ) (increment : ℕ → ℝ) :
    FiniteSurvivesNonnegative
        (Combinatorics.Sequence.blockCoordinates start n increment) ↔
      SurvivesNonnegative n (fun k => increment (start + k)) := by
  have hsum (k : Fin n) :
      (∑ j : Fin (k + 1),
        Combinatorics.Sequence.blockCoordinates start n increment
          ⟨j, lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt k.isLt)⟩) =
        AdditivePath.displacement (k + 1)
          (fun t => increment (start + t)) := by
    simp only [Combinatorics.Sequence.blockCoordinates,
      AdditivePath.displacement]
    exact Fin.sum_univ_eq_sum_range
      (fun t => increment (start + t)) (k + 1)
  constructor <;> intro h k
  · simpa only [hsum k] using h k
  · simpa only [hsum k] using h k

/-- The finite survival condition is a measurable subset of the space of
finite increment blocks. -/
theorem measurableSet_finiteSurvivesNonnegative (n : ℕ) :
    MeasurableSet {block : Fin n → ℝ | FiniteSurvivesNonnegative block} := by
  rw [show {block : Fin n → ℝ | FiniteSurvivesNonnegative block} =
      ⋂ k : Fin n,
        {block | 0 ≤ ∑ j : Fin (k + 1),
          block ⟨j, lt_of_lt_of_le j.isLt
            (Nat.succ_le_of_lt k.isLt)⟩} by
    ext block
    simp [FiniteSurvivesNonnegative]]
  apply MeasurableSet.iInter
  intro k
  have hmeas : Measurable (fun block : Fin n → ℝ =>
      ∑ j : Fin (k + 1),
        block ⟨j, lt_of_lt_of_le j.isLt
          (Nat.succ_le_of_lt k.isLt)⟩) := by
    exact Finset.measurable_sum Finset.univ fun j _ =>
      measurable_pi_apply
        (⟨j, lt_of_lt_of_le j.isLt
          (Nat.succ_le_of_lt k.isLt)⟩ : Fin n)
  exact measurableSet_Ici.preimage hmeas

/-- The finite survival event is measurable. -/
theorem measurableSet_survivesNonnegative (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ | SurvivesNonnegative n increment} := by
  rw [show {increment : ℕ → ℝ | SurvivesNonnegative n increment} =
      ⋂ k : Fin n,
        {increment | 0 ≤ AdditivePath.displacement (k + 1) increment} by
    ext increment
    simp [SurvivesNonnegative]]
  exact MeasurableSet.iInter fun k =>
    measurableSet_Ici.preimage (displacement_measurable (k + 1))

/-- Survival through a longer horizon implies survival through every
shorter horizon. -/
theorem SurvivesNonnegative.mono
    {n m : ℕ} (hnm : n ≤ m) {increment : ℕ → ℝ}
    (h : SurvivesNonnegative m increment) :
    SurvivesNonnegative n increment := by
  intro k
  exact h ⟨k, lt_of_lt_of_le k.isLt hnm⟩

/-- Survival through time `n` includes the nonnegative initial value. -/
theorem SurvivesNonnegative.displacement_nonneg
    {n : ℕ} {increment : ℕ → ℝ}
    (h : SurvivesNonnegative n increment) {k : ℕ} (hk : k ≤ n) :
    0 ≤ AdditivePath.displacement k increment := by
  cases k with
  | zero => simp [AdditivePath.displacement_zero]
  | succ j =>
      have hj : j < n := by omega
      simpa using h ⟨j, hj⟩

/-- A shifted window survives exactly when all positions in that window
lie above its starting position. This is the finite-window condition used
in the path transform described in Vladislav Vysotsky, *Positivity of
integrated random walks*, Ann. Inst. H. Poincaré Probab. Stat. 50(1)
(2014), Section 3.1, equation (17), DOI 10.1214/12-AIHP487. -/
theorem SurvivesNonnegative.shift_iff
    (n start : ℕ) (increment : ℕ → ℝ) :
    SurvivesNonnegative n (fun k => increment (start + k)) ↔
      ∀ j : Fin n,
        AdditivePath.displacement start increment ≤
          AdditivePath.displacement (start + (j + 1)) increment := by
  constructor
  · intro h j
    have hj := h j
    rw [AdditivePath.displacement_add]
    linarith
  · intro h j
    have hj := h j
    rw [AdditivePath.displacement_add] at hj
    linarith

/-- The first length-`n` surviving window starts at `start`: the window at
`start` survives, and every earlier window fails. This is the discrete
first-window event in the path transform of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480–485, DOI 10.1214/aop/1176996098;
see also Vladislav Vysotsky, *Positivity of integrated random walks*,
Section 3.1, equation (17), DOI 10.1214/12-AIHP487. -/
def IsFirstSurvivingWindow (n start : ℕ) (increment : ℕ → ℝ) : Prop :=
  SurvivesNonnegative n (fun k => increment (start + k)) ∧
    ∀ j : Fin start,
      ¬ SurvivesNonnegative n (fun k => increment (j + k))

/-- Each finite-time first surviving window is a measurable event of the
increment sequence. -/
theorem measurableSet_isFirstSurvivingWindow (n start : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      IsFirstSurvivingWindow n start increment} := by
  rw [show {increment : ℕ → ℝ |
        IsFirstSurvivingWindow n start increment} =
      {increment | SurvivesNonnegative n
        (fun k => increment (start + k))} ∩
        ⋂ j : Fin start,
          {increment | SurvivesNonnegative n
            (fun k => increment (j + k))}ᶜ by
    ext increment
    simp [IsFirstSurvivingWindow]]
  exact ((measurableSet_survivesNonnegative n).preimage
      (measurable_natAdd start)).inter
    (MeasurableSet.iInter fun j : Fin start =>
      ((measurableSet_survivesNonnegative n).preimage
        (measurable_natAdd j)).compl)

/-- A first surviving window has only one starting time. -/
theorem IsFirstSurvivingWindow.unique
    {n start other : ℕ} {increment : ℕ → ℝ}
    (hstart : IsFirstSurvivingWindow n start increment)
    (hother : IsFirstSurvivingWindow n other increment) :
    start = other := by
  rcases lt_trichotomy start other with h | h | h
  · exact False.elim (hother.2 ⟨start, h⟩ hstart.1)
  · exact h
  · exact False.elim (hstart.2 ⟨other, h⟩ hother.1)

/-- Among the surviving windows up to a given starting time, one begins
first. -/
theorem exists_firstSurvivingWindow_le
    {n start : ℕ} {increment : ℕ → ℝ}
    (h : SurvivesNonnegative n (fun k => increment (start + k))) :
    ∃ first ≤ start, IsFirstSurvivingWindow n first increment := by
  classical
  let hex : ∃ j : ℕ,
      SurvivesNonnegative n (fun k => increment (j + k)) := ⟨start, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, ?_⟩
  intro j
  exact Nat.find_min hex j.isLt

/-- A surviving walk has a nonnegative normalized step path for every time
in the unit interval when the spatial scale is positive. -/
theorem SurvivesNonnegative.normalizedStepCadlagPathIcc_nonnegative
    {n : ℕ} {increment : ℕ → ℝ}
    (h : SurvivesNonnegative n increment)
    (scale : ℕ → ℝ) (hscale : 0 < scale n) :
    ∀ t : unitInterval,
      0 ≤ normalizedStepCadlagPathIcc scale n increment t := by
  intro t
  have htime := natFloor_mul_le_of_mem_unitInterval n t
  have hdisp := h.displacement_nonneg htime
  change 0 ≤ (scale n)⁻¹ *
    AdditivePath.displacement ⌊(n : ℝ) * (t : ℝ)⌋₊ increment
  exact mul_nonneg (inv_nonneg.mpr hscale.le) hdisp

/-- Nonnegative grid values give a nonnegative polygonal interpolation. -/
theorem SurvivesNonnegative.normalizedLinearCadlagPathIcc_nonnegative
    {n : ℕ} {increment : ℕ → ℝ}
    (h : SurvivesNonnegative n increment)
    (scale : ℕ → ℝ) (hn : 0 < n) (hscale : 0 < scale n) :
    ∀ t : unitInterval,
      0 ≤ normalizedLinearCadlagPathIcc scale n increment t := by
  have hgrid : ∀ k : Fin n,
      (scale n)⁻¹ * AdditivePath.displacement (k + 1) increment ∈
        Set.Ici 0 := by
    intro k
    exact mul_nonneg (inv_nonneg.mpr hscale.le) (h k)
  have hrange : Set.range
      (normalizedLinearContinuousPathIcc scale n increment) ⊆
        Set.Ici 0 :=
    (normalizedLinearContinuousPathIcc_range_subset_iff
      scale hn (convex_Ici 0) (le_refl 0) increment).2 hgrid
  intro t
  exact hrange ⟨t, rfl⟩

end ProbabilityTheory.RandomWalk

end
