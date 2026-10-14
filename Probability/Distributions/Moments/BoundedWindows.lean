/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Signs

/-!
# Positive-mass bounded increment windows

The public theorems in this file are:

- `ProbabilityTheory.IsCenteredSecondMoment.exists_pos_Icc_measure_pos`:
  for a centered law with variance $\sigma^2>0$, there exist
  $0<a<b$ with $\nu([a,b])>0$.
- `ProbabilityTheory.IsCenteredSecondMoment.exists_reflected_pos_Icc_measure_pos`:
  there exist $0<a<b$ with
  $(\nu\circ(x\mapsto-x)^{-1})([a,b])>0$.

These are the bounded positive and negative increment windows selected
in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Appendix A.2, proof of the meander transition lemma
used in Chapter 3, Lemma 3.5.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- A centered nondegenerate finite-variance increment law charges a
bounded closed interval of strictly positive increments. -/
theorem IsCenteredSecondMoment.exists_pos_Icc_measure_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ 0 < ν (Set.Icc a b) := by
  obtain ⟨a, b, ha, hab, hmass⟩ := hν.exists_pos_interval_measure_pos hsigma
  refine ⟨a, b, ha, hab, hmass.trans_le ?_⟩
  exact measure_mono Set.Ioo_subset_Icc_self

/-- The reflected law charges a bounded closed interval of strictly
positive reflected increments. -/
theorem IsCenteredSecondMoment.exists_reflected_pos_Icc_measure_pos
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      0 < (ν.map fun x : ℝ => -x) (Set.Icc a b) := by
  obtain ⟨lower, upper, hlt, hneg, hmass⟩ :=
    hν.exists_neg_interval_measure_pos hsigma
  refine ⟨-upper, -lower, by linarith, by linarith, ?_⟩
  rw [Measure.map_apply measurable_neg measurableSet_Icc]
  exact hmass.trans_le (measure_mono (by
    intro x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩))

end ProbabilityTheory

end
