/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.FiniteTime
public import Probability.Process.Brownian.AboveStart.FirstWindow.Basic

/-!
# Approximation by finite first-window times

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendsto_measure_noFirstWindow`:
  for a centered unit-variance random walk, the probability that the
  normalized polygonal path has no eligible unit window tends to zero.

This is the probability comparison following equations (3.5)--(3.7) in
Erwin Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Theorem 3.2, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. For each fixed cutoff $s$,
the unrestricted failure event lies inside the failure event for $T^s$;
its limiting Brownian probability tends to zero as $s\to\infty$.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The normalized walk eventually has an eligible unit window with
probability tending to one. -/
theorem tendsto_measure_noFirstWindow
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    Tendsto (fun n => (iidSequenceLaw ν)
      {increment | firstNonnegativeWindowStart
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment) = ⊤})
      atTop (nhds 0) := by
  let a : ℕ → ℝ≥0∞ := fun n => (iidSequenceLaw ν)
    {increment | firstNonnegativeWindowStart
      (normalizedLinearContinuousPathUnbounded
        (fun n => Real.sqrt n) n increment) = ⊤}
  let b : ℕ → ℕ → ℝ≥0∞ := fun k n => (iidSequenceLaw ν)
    {increment | firstNonnegativeWindowStartUpTo
      (normalizedLinearContinuousPathUnbounded
        (fun n => Real.sqrt n) n increment) ((k : ℝ≥0) + 1) = ⊤}
  let c : ℕ → ℝ≥0∞ := fun k => P
    {ω | firstNonnegativeWindowStartUpTo
      (hB.continuousPathMap hmeasurable ω) ((k : ℝ≥0) + 1) = ⊤}
  have hbound (k n : ℕ) : a n ≤ b k n := by
    apply measure_mono
    intro increment hfirst
    have hle := firstNonnegativeWindowStart_le_upTo
      (normalizedLinearContinuousPathUnbounded
        (fun n => Real.sqrt n) n increment) ((k : ℝ≥0) + 1)
    rw [hfirst] at hle
    exact top_unique hle
  have hb (k : ℕ) : Tendsto (b k) atTop (nhds (c k)) := by
    simpa only [b, c] using tendsto_measure_noFiniteFirstWindow
      ν hcentered hsecondMoment hB hcontinuous hmeasurable
      ((k : ℝ≥0) + 1) (k + 1) (Nat.succ_pos k) (by simp)
  have hc : Tendsto c atTop (nhds 0) :=
    hB.tendsto_measure_firstNonnegativeWindowStartUpTo_eq_top hmeasurable
  change Tendsto a atTop (nhds 0)
  apply tendsto_order.mpr
  constructor
  · intro x hx
    exact (not_lt_zero hx).elim
  · intro ε hε
    obtain ⟨k, hk⟩ : ∃ k, c k < ε :=
      (hc.eventually (isOpen_Iio.mem_nhds hε)).exists
    have hbevent : ∀ᶠ n in atTop, b k n < ε :=
      (hb k).eventually (isOpen_Iio.mem_nhds hk)
    filter_upwards [hbevent] with n hn
    exact (hbound k n).trans_lt hn

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
