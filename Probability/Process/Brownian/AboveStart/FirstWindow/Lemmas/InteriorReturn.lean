/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.Path.Transform.Continuous

import Probability.Process.Brownian.Independence.PastFuturePaths
import Probability.Process.Brownian.Reflection.FirstPassage.Principle
import Probability.Process.Path.AboveStart.FirstWindow.EndpointReturn.Basic
import Probability.Process.Path.Extrema.RunningMinimum
import Topology.Order.NNReal.Rational
import Probability.Independence.NullSections
import all Probability.Process.Path.AboveStart.FirstWindow.EndpointReturn.Lemmas.RationalCover

/-!
# Interior returns of the first Brownian unit window

## Internal proof declarations

The supporting lemmas in this file are:

- `ProbabilityTheory.IsBrownianReal.measure_tripleRunningMinimumContact_eq_zero`:
  Bolthausen's three-contact event $U$ has probability zero.

- `ProbabilityTheory.IsBrownianReal.measure_pastMinimumGap_eq_futureMinimum`:
  the equality event between the past minimum gap and the future running
  minimum has probability zero.
- `ProbabilityTheory.IsBrownianReal.measure_repeatedMinimumOnInterval_eq_zero`:
  a repeated minimum level on a later interval with constant running minimum
  forms a null event.
- `ProbabilityTheory.IsBrownianReal.measure_rationalRepeatedMinimum_eq_zero`:
  the countable union of these rational-interval events is null.

- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStart_interiorReturn_eq_zero`:
  the same assertion for the unrestricted first unit window.

This is equation (2.4) of Lemma 2.3 in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. The proof uses Bolthausen's countable
rational-interval covering of repeated running-minimum values. Bolthausen
first introduces an event with three zeros of the height above the minimum.
For a return inside the first unit window, the first-window identity already
fixes the running minimum throughout the window, so its two return times
give the same rational-interval event directly.
-/

section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- The minimum of the future increment path almost surely differs
from the gap between the past minimum and the present Brownian value.
The two variables are independent and the future minimum is atomless. -/
lemma IsBrownianReal.measure_pastMinimumGap_eq_futureMinimum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    (r : ℝ≥0) {d : ℝ≥0} (hd : 0 < d) :
    let shifted : ℝ≥0 → Ω → ℝ := fun u ω => B (r + u) ω - B r ω
    let hshift : IsBrownianReal shifted P := hB.shift r
    let hshiftMeas : ∀ u, Measurable (shifted u) :=
      fun u => (hBmeasurable (r + u)).sub (hBmeasurable r)
    P {ω | runningMinimum (hB.continuousPathMap hBmeasurable ω) r -
      hB.continuousPathMap hBmeasurable ω r =
        runningMinimum (hshift.continuousPathMap hshiftMeas ω) d} = 0 := by
  dsimp
  let shifted : ℝ≥0 → Ω → ℝ := fun u ω => B (r + u) ω - B r ω
  let hshift : IsBrownianReal shifted P := hB.shift r
  let hshiftMeas (u : ℝ≥0) : Measurable (shifted u) :=
    (hBmeasurable (r + u)).sub (hBmeasurable r)
  let pathB := hB.continuousPathMap hBmeasurable
  let pathF := hshift.continuousPathMap hshiftMeas
  let X : Ω → ℝ := fun ω => runningMinimum (pathB ω) r - pathB ω r
  let Y : Ω → ℝ := fun ω => runningMinimum (pathF ω) d
  have hX : Measurable X :=
    ((measurable_runningMinimum r).comp
      (hB.measurable_continuousPathMap hBmeasurable)).sub
      ((ContinuousMap.measurable_eval r).comp
        (hB.measurable_continuousPathMap hBmeasurable))
  have hY : Measurable Y :=
    (measurable_runningMinimum d).comp
      (hshift.measurable_continuousPathMap hshiftMeas)
  have hPathInd := hB.indepFun_shiftPath_freezePath hBmeasurable r
  have hφ : Measurable (fun f : C(ℝ≥0, ℝ) =>
      runningMinimum f r - f r) :=
    (measurable_runningMinimum r).sub (ContinuousMap.measurable_eval r)
  have hInd : X ⟂ᵢ[P] Y := by
    have hInd' := hPathInd.symm.comp hφ (measurable_runningMinimum d)
    have hXeq : X = (fun ω =>
        runningMinimum (freezeAfter (pathB ω) r) r -
          freezeAfter (pathB ω) r r) := by
      funext ω
      change runningMinimum (pathB ω) r - (pathB ω) r =
        runningMinimum (freezeAfter (pathB ω) r) r -
          (freezeAfter (pathB ω) r) r
      rw [runningMinimum_freezeAfter_eq (pathB ω) (le_refl r)]
      simp [freezeAfter]
    rw [hXeq]
    exact hInd'
  letI : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  have hnull (a : ℝ) : (P.map Y) {a} = 0 := by
    have hset : MeasurableSet {f : C(ℝ≥0, ℝ) |
        runningMinimum f d = a} :=
      (measurable_runningMinimum d) (measurableSet_singleton a)
    calc
      (P.map Y) {a} = P {ω | Y ω = a} := by
        rw [Measure.map_apply hY (measurableSet_singleton a)]
        rfl
      _ = (P.map pathF) {f : C(ℝ≥0, ℝ) | runningMinimum f d = a} := by
        rw [Measure.map_apply (hshift.measurable_continuousPathMap hshiftMeas) hset]
        rfl
      _ = 0 := hshift.measure_runningMinimum_eq hshiftMeas hd a
  exact hInd.measure_eq_zero_of_right_atomless hX hY hnull

/-- A level already attained by the running minimum before `r` cannot
be attained again during an interval `[r,q]` on which the running
minimum remains constant. This is the fixed rational-interval event
in Bolthausen's Lemma 2.3, equation (2.4). -/
lemma IsBrownianReal.measure_repeatedMinimumOnInterval_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {r q : ℝ≥0} (hrq : r < q) :
    P {ω | runningMinimum (hB.continuousPathMap hBmeasurable ω) q =
        runningMinimum (hB.continuousPathMap hBmeasurable ω) r ∧
      ∃ v, r ≤ v ∧ v ≤ q ∧
        hB.continuousPathMap hBmeasurable ω v =
          runningMinimum (hB.continuousPathMap hBmeasurable ω) r} = 0 := by
  let shifted : ℝ≥0 → Ω → ℝ := fun u ω => B (r + u) ω - B r ω
  let hshift : IsBrownianReal shifted P := hB.shift r
  let hshiftMeas (u : ℝ≥0) : Measurable (shifted u) :=
    (hBmeasurable (r + u)).sub (hBmeasurable r)
  let pathB := hB.continuousPathMap hBmeasurable
  let pathF := hshift.continuousPathMap hshiftMeas
  have hPathEq : pathF =ᵐ[P] fun ω => shiftToZero (pathB ω) r := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hshift.continuousPathMap_ae_eq hshiftMeas] with ω hω hωF
    ext u
    change pathF ω u = pathB ω (r + u) - pathB ω r
    rw [hωF u, hω (r + u), hω r]
  have hPathNull : P {ω | pathF ω ≠ shiftToZero (pathB ω) r} = 0 :=
    (ae_iff).mp hPathEq
  have hMinimumNull :
      P {ω | runningMinimum (pathB ω) r - pathB ω r =
        runningMinimum (pathF ω) (q - r)} = 0 :=
    hB.measure_pastMinimumGap_eq_futureMinimum hBmeasurable r
      (tsub_pos_iff_lt.mpr hrq)
  apply measure_mono_null (s := {ω | runningMinimum (pathB ω) q =
      runningMinimum (pathB ω) r ∧
    ∃ v, r ≤ v ∧ v ≤ q ∧ pathB ω v = runningMinimum (pathB ω) r})
    (t := {ω | runningMinimum (pathB ω) r - pathB ω r =
      runningMinimum (pathF ω) (q - r)} ∪
      {ω | pathF ω ≠ shiftToZero (pathB ω) r}) ?_
    (measure_union_null hMinimumNull hPathNull)
  intro ω hω
  obtain ⟨hflat, v, hrv, hvq, hrecord⟩ := hω
  by_cases heq : pathF ω = shiftToZero (pathB ω) r
  · left
    change runningMinimum (pathB ω) r - pathB ω r =
      runningMinimum (pathF ω) (q - r)
    rw [heq]
    exact (runningMinimum_shiftToZero_eq_of_record (pathB ω)
      hrv hvq hflat hrecord).symm
  · exact Or.inr heq

/-- The countable union of fixed rational-interval events in
Bolthausen's Lemma 2.3 has Brownian probability zero. -/
lemma IsBrownianReal.measure_rationalRepeatedMinimum_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    P {ω | ∃ r q : ℚ≥0,
      (r : ℝ≥0) < (q : ℝ≥0) ∧
      runningMinimum (hB.continuousPathMap hBmeasurable ω)
        ((q : ℝ≥0)) =
        runningMinimum (hB.continuousPathMap hBmeasurable ω)
          ((r : ℝ≥0)) ∧
      ∃ v, (r : ℝ≥0) ≤ v ∧
        v ≤ (q : ℝ≥0) ∧
        hB.continuousPathMap hBmeasurable ω v =
          runningMinimum (hB.continuousPathMap hBmeasurable ω)
            ((r : ℝ≥0))} = 0 := by
  let pathB := hB.continuousPathMap hBmeasurable
  let E : ℚ≥0 → ℚ≥0 → Set Ω := fun r q =>
    {ω | (r : ℝ≥0) < (q : ℝ≥0) ∧
      runningMinimum (pathB ω) ((q : ℝ≥0)) =
        runningMinimum (pathB ω) ((r : ℝ≥0)) ∧
      ∃ v, (r : ℝ≥0) ≤ v ∧
        v ≤ (q : ℝ≥0) ∧
        pathB ω v = runningMinimum (pathB ω) ((r : ℝ≥0))}
  have hEnull (r q : ℚ≥0) : P (E r q) = 0 := by
    by_cases hrq : (r : ℝ≥0) < (q : ℝ≥0)
    · simpa only [E, hrq, true_and] using
        hB.measure_repeatedMinimumOnInterval_eq_zero hBmeasurable hrq
    · have hrqRat : ¬ r < q := by exact_mod_cast hrq
      simp [E, hrqRat]
  have hUnion : P (⋃ r : ℚ≥0, ⋃ q : ℚ≥0, E r q) = 0 :=
    measure_iUnion_null fun r => measure_iUnion_null fun q => hEnull r q
  have hset :
      {ω | ∃ r q : ℚ≥0,
        (r : ℝ≥0) < (q : ℝ≥0) ∧
        runningMinimum (pathB ω) ((q : ℝ≥0)) =
          runningMinimum (pathB ω) ((r : ℝ≥0)) ∧
        ∃ v, (r : ℝ≥0) ≤ v ∧
          v ≤ (q : ℝ≥0) ∧
          pathB ω v = runningMinimum (pathB ω) ((r : ℝ≥0))} =
      ⋃ r : ℚ≥0, ⋃ q : ℚ≥0, E r q := by
    ext ω
    simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion]
  exact hset ▸ hUnion


/-- The event `U` introduced in the proof of Bolthausen's Lemma 2.3
has Brownian probability zero. Its three contacts yield the countable
rational-interval covering used there. -/
lemma IsBrownianReal.measure_tripleRunningMinimumContact_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    P {ω | HasTripleRunningMinimumContact
      (hB.continuousPathMap hBmeasurable ω)} = 0 := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hcover :
      {ω | HasTripleRunningMinimumContact (pathB ω)} ⊆
      {ω | ∃ r q : ℚ≥0,
        (r : ℝ≥0) < (q : ℝ≥0) ∧
        runningMinimum (pathB ω) ((q : ℝ≥0)) =
          runningMinimum (pathB ω) ((r : ℝ≥0)) ∧
        ∃ v, (r : ℝ≥0) ≤ v ∧
          v ≤ (q : ℝ≥0) ∧
          pathB ω v = runningMinimum (pathB ω) ((r : ℝ≥0))} := by
    intro ω hω
    exact hω.rationalInterval
  exact measure_mono_null hcover
    (hB.measure_rationalRepeatedMinimum_eq_zero hBmeasurable)

/-- Bolthausen's Lemma 2.3, equation (2.4): almost surely there is no
interior return to the starting level of the first qualifying unit
window before a fixed horizon. -/
private lemma IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_interiorReturn_eq_zero
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
  have hcover :
      {ω | ∃ t u : ℝ≥0,
        firstNonnegativeWindowStartUpTo (pathB ω) s = t ∧
        0 < u ∧ u < 1 ∧ pathB ω (t + u) = pathB ω t} ⊆
      {ω | ∃ r q : ℚ≥0,
        (r : ℝ≥0) < (q : ℝ≥0) ∧
        runningMinimum (pathB ω) ((q : ℝ≥0)) =
          runningMinimum (pathB ω) ((r : ℝ≥0)) ∧
        ∃ v, (r : ℝ≥0) ≤ v ∧
          v ≤ (q : ℝ≥0) ∧
          pathB ω v = runningMinimum (pathB ω) ((r : ℝ≥0))} := by
    intro ω hω
    obtain ⟨t, u, hfirst, hu0, hu1, hreturn⟩ := hω
    exact firstNonnegativeWindowStartUpTo_return_rationalInterval
      (pathB ω) s t hfirst hu0 hu1 hreturn
  exact measure_mono_null hcover
    (hB.measure_rationalRepeatedMinimum_eq_zero hBmeasurable)

/-- Bolthausen's Lemma 2.3, equation (2.4), for the unrestricted
first unit window. Finite-horizon versions cover the event as the
horizon ranges over natural numbers. -/
lemma IsBrownianReal.measure_firstNonnegativeWindowStart_interiorReturn_eq_zero
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
