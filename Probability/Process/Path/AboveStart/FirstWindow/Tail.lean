/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.Continuous
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Tail of the first eligible-window time

The public theorem in this file is:

- `ProbabilityTheory.tendsto_measure_firstNonnegativeWindowStartUpTo_ne_top`:
  for a probability law on continuous paths under which $T<\infty$
  almost surely, the probability of $T^{n+1}<\infty$ tends to one.

This is the monotone-exhaustion step used to choose the cutoff $c$ in
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Theorem 3.2, equation (3.5),
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory
open scoped NNReal

/-- The finite-horizon first-window events increase to the unrestricted
first-window event. Hence their probabilities tend to one under almost-sure
finiteness of the unrestricted first-window time. -/
theorem tendsto_measure_firstNonnegativeWindowStartUpTo_ne_top
    (μ : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure μ]
    (hfinite : μ {f | firstNonnegativeWindowStart f ≠ ⊤} = 1) :
    Tendsto (fun n : ℕ => μ {f | firstNonnegativeWindowStartUpTo f
      ((n : ℝ≥0) + 1) ≠ ⊤}) atTop (nhds 1) := by
  let A : ℕ → Set C(ℝ≥0, ℝ) := fun n =>
    {f | firstNonnegativeWindowStartUpTo f ((n : ℝ≥0) + 1) ≠ ⊤}
  have hAmono : Monotone A := by
    intro n m hnm f hf
    have hcut : (n : ℝ≥0) + 1 ≤ (m : ℝ≥0) + 1 := by
      gcongr
    have htime := firstNonnegativeWindowStartUpTo_mono f hcut
    exact WithTop.lt_top_iff_ne_top.mp
      (lt_of_le_of_lt htime (WithTop.lt_top_iff_ne_top.mpr hf))
  have hunion : (⋃ n, A n) =
      {f | firstNonnegativeWindowStart f ≠ ⊤} := by
    ext f
    simp only [Set.mem_iUnion, A, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      have heq := firstNonnegativeWindowStartUpTo_eq_first_of_ne_top
        f ((n : ℝ≥0) + 1) hn
      rw [← heq]
      exact hn
    · intro hf
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hf
      obtain ⟨n, hn⟩ := exists_nat_ge t
      have hcut : t + 1 ≤ (n : ℝ≥0) + 1 := by
        gcongr
      have heq := firstNonnegativeWindowStartUpTo_eq_first_of_le
        f ht.symm hcut
      refine ⟨n, ?_⟩
      rw [heq]
      exact WithTop.coe_ne_top
  have hlimit := tendsto_measure_iUnion_atTop (μ := μ) (s := A) hAmono
  change Tendsto (fun n => μ (A n)) atTop (nhds (μ (⋃ n, A n))) at hlimit
  rw [hunion, hfinite] at hlimit
  exact hlimit

end ProbabilityTheory

end
