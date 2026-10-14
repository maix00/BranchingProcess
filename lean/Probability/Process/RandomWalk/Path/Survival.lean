/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.Basic
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

end ProbabilityTheory.RandomWalk

end
