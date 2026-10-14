/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Independence.PastFuturePaths
public import Probability.Process.Path.AboveStart.RunningMinimum

/-!
# Interior returns of the first Brownian unit window

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_interiorReturn_eq_zero`:
  for a finite horizon $s$, the first unit window of a Brownian path
  almost surely does not return to its starting value at an interior time.
- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStart_interiorReturn_eq_zero`:
  the same assertion for the unrestricted first unit window.

This is equation (2.4) of Lemma 2.3 in Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. The proof uses Bolthausen's countable
rational-interval covering of repeated running-minimum values. Bolthausen
first introduces an event with three zeros of the height above the minimum.
For a return inside the first unit window, the first-window identity already
fixes the running minimum throughout the window, so its two return times
give the same rational-interval event directly.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Bolthausen's Lemma 2.3, equation (2.4): almost surely there is no
interior return to the starting level of the first qualifying unit
window before a fixed horizon. -/
theorem IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_interiorReturn_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (s : ℝ≥0) :
    P {ω | ∃ t u : ℝ≥0,
      firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hBmeasurable ω) s = t ∧
      0 < u ∧ u < 1 ∧
      hB.continuousPathMap hBmeasurable ω (t + u) =
        hB.continuousPathMap hBmeasurable ω t} = 0 := by
  let pathB := hB.continuousPathMap hBmeasurable
  let E : ℚ≥0 → ℚ≥0 → Set Ω := fun r q =>
    {ω | nonnegativeRationalTime r < nonnegativeRationalTime q ∧
      runningMinimum (pathB ω) (nonnegativeRationalTime q) =
        runningMinimum (pathB ω) (nonnegativeRationalTime r) ∧
      ∃ v, nonnegativeRationalTime r ≤ v ∧
        v ≤ nonnegativeRationalTime q ∧
        pathB ω v = runningMinimum (pathB ω) (nonnegativeRationalTime r)}
  have hEnull (r q : ℚ≥0) : P (E r q) = 0 := by
    by_cases hrq : nonnegativeRationalTime r < nonnegativeRationalTime q
    · simpa only [E, hrq, true_and] using
        hB.measure_repeatedMinimumOnInterval_eq_zero hBmeasurable hrq
    · simp [E, hrq]
  have hcover :
      {ω | ∃ t u : ℝ≥0,
        firstNonnegativeWindowStartUpTo (pathB ω) s = t ∧
        0 < u ∧ u < 1 ∧ pathB ω (t + u) = pathB ω t} ⊆
      ⋃ r : ℚ≥0, ⋃ q : ℚ≥0, E r q := by
    intro ω hω
    obtain ⟨t, u, hfirst, hu0, hu1, hreturn⟩ := hω
    obtain ⟨r, q, hrq, hflat, v, hrv, hvq, hrecord⟩ :=
      firstNonnegativeWindowStartUpTo_return_rationalInterval
        (pathB ω) s t hfirst hu0 hu1 hreturn
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
      ⟨q, ⟨hrq, hflat, v, hrv, hvq, hrecord⟩⟩⟩
  exact measure_mono_null hcover
    (measure_iUnion_null fun r => measure_iUnion_null fun q => hEnull r q)

/-- Bolthausen's Lemma 2.3, equation (2.4), for the unrestricted
first unit window. Finite-horizon versions cover the event as the
horizon ranges over natural numbers. -/
theorem IsBrownianReal.measure_firstNonnegativeWindowStart_interiorReturn_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    P {ω | ∃ t u : ℝ≥0,
      firstNonnegativeWindowStart
        (hB.continuousPathMap hBmeasurable ω) = t ∧
      0 < u ∧ u < 1 ∧
      hB.continuousPathMap hBmeasurable ω (t + u) =
        hB.continuousPathMap hBmeasurable ω t} = 0 := by
  let pathB := hB.continuousPathMap hBmeasurable
  let E : ℕ → Set Ω := fun n =>
    {ω | ∃ t u : ℝ≥0,
      firstNonnegativeWindowStartUpTo (pathB ω) n = t ∧
      0 < u ∧ u < 1 ∧ pathB ω (t + u) = pathB ω t}
  have hEnull (n : ℕ) : P (E n) = 0 :=
    hB.measure_firstNonnegativeWindowStartUpTo_interiorReturn_eq_zero
      hBmeasurable n
  have hcover :
      {ω | ∃ t u : ℝ≥0,
        firstNonnegativeWindowStart (pathB ω) = t ∧
        0 < u ∧ u < 1 ∧ pathB ω (t + u) = pathB ω t} ⊆
      ⋃ n : ℕ, E n := by
    intro ω hω
    obtain ⟨t, u, hfirst, hu0, hu1, hreturn⟩ := hω
    obtain ⟨n, hn⟩ := exists_nat_ge (t + 1)
    have hfirstn := firstNonnegativeWindowStartUpTo_eq_first_of_le
      (pathB ω) (s := n) hfirst hn
    exact Set.mem_iUnion.mpr ⟨n, ⟨t, u, hfirstn, hu0, hu1, hreturn⟩⟩
  exact measure_mono_null hcover (measure_iUnion_null hEnull)

end ProbabilityTheory

end
