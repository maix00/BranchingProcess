/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.InteriorDiffusive

/-!
# Middle-start estimate for the moving entrance corridor

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.movingTransitionEvent`:
  $cj/\Delta^2\le x+S_j\le\Delta+cj/\Delta^2$ for
  $1\le j\le n$, with terminal position in
  $[cn/\Delta^2+\Delta/3,cn/\Delta^2+2\Delta/3]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteInteriorEvent_subset_movingTransitionEvent`:
  the middle-start constant corridor is contained in the moving event.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.eventually_middleMovingTransitionProbability_pos`:
  for $n_\Delta=\lfloor\Delta^2\rfloor$, the moving event has a
  uniform positive lower bound over $x\in[\Delta/12,11\Delta/12]$.

This is the middle starting interval in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma used in Chapter 3,
Lemma 3.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The moving entrance event `A_Delta(x)` at a finite horizon. -/
def movingTransitionEvent (n : ℕ) (width drift start : ℝ) :
    Set (ℕ → ℝ) :=
  {increment |
    (∀ k : Fin n,
      drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤
        start + AdditivePath.displacement (k + 1) increment ∧
      start + AdditivePath.displacement (k + 1) increment ≤
        width + drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2) ∧
    drift * (n : ℝ) / width ^ 2 + width / 3 ≤
      start + AdditivePath.displacement n increment ∧
    start + AdditivePath.displacement n increment ≤
      drift * (n : ℝ) / width ^ 2 + 2 * width / 3}

/-- The constant interior corridor used in the middle-start Donsker
argument lies inside the moving corridor of Wang Yiyang, Appendix A.2. -/
theorem finiteInteriorEvent_subset_movingTransitionEvent
    {n : ℕ} {width drift start : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hn : (n : ℝ) ≤ width ^ 2)
    (hlarge : 12 * drift ≤ width) :
    FunctionalLimit.Donsker.finiteInteriorEvent n width drift start ⊆
      movingTransitionEvent n width drift start := by
  intro increment hinc
  have hwidthSq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  constructor
  · intro k
    have hkNat : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
    have hk : (((k.val + 1 : ℕ) : ℝ)) ≤ width ^ 2 :=
      (Nat.cast_le.mpr hkNat).trans hn
    have hshiftNonneg :
        0 ≤ drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 :=
      div_nonneg (mul_nonneg hdrift (Nat.cast_nonneg _)) hwidthSq.le
    have hshiftLe :
        drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤ drift := by
      apply (div_le_iff₀ hwidthSq).2
      exact mul_le_mul_of_nonneg_left hk hdrift
    have hgrid := hinc.1 k
    exact ⟨hshiftLe.trans hgrid.1,
      hgrid.2.trans (le_add_of_nonneg_right hshiftNonneg)⟩
  · have hshiftNonneg : 0 ≤ drift * (n : ℝ) / width ^ 2 :=
      div_nonneg (mul_nonneg hdrift (Nat.cast_nonneg _)) hwidthSq.le
    have hshiftLe : drift * (n : ℝ) / width ^ 2 ≤ drift := by
      exact (div_le_iff₀ hwidthSq).2
        (mul_le_mul_of_nonneg_left hn hdrift)
    constructor
    · calc
        drift * (n : ℝ) / width ^ 2 + width / 3 ≤
            drift + width / 3 := by linarith
        _ ≤ 5 / 12 * width := by linarith
        _ ≤ start + AdditivePath.displacement n increment := hinc.2.1
    · calc
        start + AdditivePath.displacement n increment ≤
            7 / 12 * width := hinc.2.2
        _ ≤ drift * (n : ℝ) / width ^ 2 + 2 * width / 3 := by
          linarith

/-- The middle starting interval of the exact moving entrance event has
a positive probability bound for all sufficiently large real widths. -/
theorem eventually_middleMovingTransitionProbability_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift : ℝ} (hdrift : 0 ≤ drift) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc (width n / 12) (11 / 12 * width n),
        q ≤ iidSequenceLaw ν
          (movingTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
            (width n) drift start) := by
  obtain ⟨q, hq, hmiddle⟩ :=
    FunctionalLimit.Donsker.eventually_diffusiveInteriorProbability_pos_uniform_of_centeredSecondMoment
      hν hsigma hwidth drift
  refine ⟨q, hq, ?_⟩
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hwidthLarge : ∀ᶠ n : ℕ in atTop, 12 * drift ≤ width n := by
    filter_upwards [hwidth.eventually (eventually_gt_atTop (12 * drift))] with n hn
    exact hn.le
  filter_upwards [hmiddle, hwidthPos, hwidthLarge] with n hn hw hl
  intro start hs
  have hfloor :
      ((Asymptotics.floorBlockLength (fun k => width k ^ 2) n : ℕ) : ℝ) ≤
        width n ^ 2 := by
    exact Nat.floor_le (sq_nonneg _)
  exact (hn start hs).trans (measure_mono
    (finiteInteriorEvent_subset_movingTransitionEvent hw hdrift hfloor hl))

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
