/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.PathLaw.ContinuousPathLaw
public import Probability.Process.Path.Independence.DenseEvaluation
public import Probability.Process.Path.Representation.Continuous
public import Probability.Process.Brownian.Reflection.FirstPassage.Principle
public import Probability.Independence.AtomlessEquality

/-!
# Brownian path independence across a deterministic time

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.indepFun_shiftPath_freezePath`:
  the path $u\mapsto B(r+u)-B(r)$ is independent of the frozen past path
  $u\mapsto B(\min(u,r))$.
- `ProbabilityTheory.IsBrownianReal.indepFun_shiftToZero_freezeAfter`:
  the same independence expressed directly through the continuous
  Brownian path map.
- `ProbabilityTheory.IsBrownianReal.measure_shiftToZero_eq`:
  the future increment path at a fixed time has the original Brownian
  path law.
- `ProbabilityTheory.IsBrownianReal.measure_pastMinimumGap_eq_futureMinimum`:
  for $d>0$, the probability that $m(r)-B(r)$ equals the minimum of
  $B(r+u)-B(r)$ over $0\le u\le d$ is zero.
- `ProbabilityTheory.IsBrownianReal.measure_repeatedMinimumOnInterval_eq_zero`:
  a Brownian running minimum constant from $r$ to $q>r$ is almost
  surely not attained at a time in $[r,q]$.
- `ProbabilityTheory.IsBrownianReal.measure_rationalRepeatedMinimum_eq_zero`:
  the union of these events over nonnegative rational intervals is null.

This is the path-valued form of the weak Markov property in mathlib's
`IsPreBrownianReal.indepFun_shift`. It supplies the independence used
for the rational-interval event in Lemma 2.3 of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- The shifted future continuous path is independent of the original
path stopped and frozen at a deterministic time. -/
theorem IsBrownianReal.indepFun_shiftPath_freezePath
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (r : ℝ≥0) :
    let shifted : ℝ≥0 → Ω → ℝ := fun u ω => B (r + u) ω - B r ω
    let hshift : IsBrownianReal shifted P := hB.shift r
    let hshiftMeas : ∀ u, Measurable (shifted u) :=
      fun u => (hBmeasurable (r + u)).sub (hBmeasurable r)
    (hshift.continuousPathMap hshiftMeas) ⟂ᵢ[P]
      (fun ω => freezeAfter (hB.continuousPathMap hBmeasurable ω) r) := by
  dsimp
  let shifted : ℝ≥0 → Ω → ℝ := fun u ω => B (r + u) ω - B r ω
  let hshift : IsBrownianReal shifted P := hB.shift r
  let hshiftMeas (u : ℝ≥0) : Measurable (shifted u) :=
    (hBmeasurable (r + u)).sub (hBmeasurable r)
  let futurePath := hshift.continuousPathMap hshiftMeas
  let pastPath : Ω → C(ℝ≥0, ℝ) :=
    fun ω => freezeAfter (hB.continuousPathMap hBmeasurable ω) r
  let rawFuture : Ω → (ℝ≥0 → ℝ) := fun ω u => shifted u ω
  let rawPast : Ω → (ℝ≥0 → ℝ) := fun ω u => B (min u r) ω
  let evaluate : (ℝ≥0 → ℝ) → (ℚ≥0 → ℝ) :=
    fun x q => x (nonnegativeRationalTime q)
  have hEval : Measurable evaluate := by
    rw [measurable_pi_iff]
    intro q
    exact measurable_pi_apply (nonnegativeRationalTime q)
  have hFreezeRaw : Measurable
      (fun x : (Set.Iic r → ℝ) => fun u : ℝ≥0 =>
        x ⟨min u r, min_le_right _ _⟩) := by
    rw [measurable_pi_iff]
    intro u
    exact measurable_pi_apply (⟨min u r, min_le_right _ _⟩ : Set.Iic r)
  have hRawInd : rawFuture ⟂ᵢ[P] rawPast := by
    have hind := hB.toIsPreBrownianReal.indepFun_shift r
    have hcomp := hind.comp measurable_id hFreezeRaw
    exact hcomp
  have hEvalInd : (evaluate ∘ rawFuture) ⟂ᵢ[P]
      (evaluate ∘ rawPast) := hRawInd.comp hEval hEval
  have hFutureAE : evaluate ∘ rawFuture =ᵐ[P]
      ContinuousMap.finiteEvaluation nonnegativeRationalTime ∘ futurePath := by
    filter_upwards [hshift.continuousPathMap_ae_eq hshiftMeas] with ω hω
    funext q
    exact (hω (nonnegativeRationalTime q)).symm
  have hPastAE : evaluate ∘ rawPast =ᵐ[P]
      ContinuousMap.finiteEvaluation nonnegativeRationalTime ∘ pastPath := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable] with ω hω
    funext q
    exact (hω (min (nonnegativeRationalTime q) r)).symm
  have hPathEvalInd := hEvalInd.congr hFutureAE hPastAE
  exact IndepFun.of_indep_finiteEvaluation nonnegativeRationalTime
    denseRange_nonnegativeRationalTime nonnegativeRationalTime
    denseRange_nonnegativeRationalTime hPathEvalInd

/-- The deterministic-time future and frozen past are independent when
both are taken from the same continuous Brownian path. -/
theorem IsBrownianReal.indepFun_shiftToZero_freezeAfter
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (r : ℝ≥0) :
    (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω) r) ⟂ᵢ[P]
      (fun ω => freezeAfter (hB.continuousPathMap hBmeasurable ω) r) := by
  let shifted : ℝ≥0 → Ω → ℝ := fun u ω => B (r + u) ω - B r ω
  let hshift : IsBrownianReal shifted P := hB.shift r
  let hshiftMeas : ∀ u, Measurable (shifted u) :=
    fun u => (hBmeasurable (r + u)).sub (hBmeasurable r)
  let pathB := hB.continuousPathMap hBmeasurable
  have hae : (fun ω => shiftToZero (pathB ω) r) =ᵐ[P]
      hshift.continuousPathMap hshiftMeas := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hshift.continuousPathMap_ae_eq hshiftMeas] with ω hω hωS
    ext u
    change pathB ω (r + u) - pathB ω r =
      hshift.continuousPathMap hshiftMeas ω u
    rw [hω (r + u), hω r, hωS u]
  exact (hB.indepFun_shiftPath_freezePath hBmeasurable r).congr hae.symm
    (ae_eq_refl _)

/-- Brownian increments after a deterministic time have Brownian path law. -/
theorem IsBrownianReal.measure_shiftToZero_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (r : ℝ≥0) :
    P.map (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω) r) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let shifted : ℝ≥0 → Ω → ℝ := fun u ω => B (r + u) ω - B r ω
  let hshift : IsBrownianReal shifted P := hB.shift r
  let hshiftMeas : ∀ u, Measurable (shifted u) :=
    fun u => (hBmeasurable (r + u)).sub (hBmeasurable r)
  let pathB := hB.continuousPathMap hBmeasurable
  have hae : (fun ω => shiftToZero (pathB ω) r) =ᵐ[P]
      hshift.continuousPathMap hshiftMeas := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hshift.continuousPathMap_ae_eq hshiftMeas] with ω hω hωS
    ext u
    change pathB ω (r + u) - pathB ω r =
      hshift.continuousPathMap hshiftMeas ω u
    rw [hω (r + u), hω r, hωS u]
  rw [Measure.map_congr hae]
  exact hshift.measure_continuousPathMap_eq hB hshiftMeas hBmeasurable

/-- The minimum of the future increment path almost surely differs
from the gap between the past minimum and the present Brownian value.
The two variables are independent and the future minimum is atomless. -/
theorem IsBrownianReal.measure_pastMinimumGap_eq_futureMinimum
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
theorem IsBrownianReal.measure_repeatedMinimumOnInterval_eq_zero
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
theorem IsBrownianReal.measure_rationalRepeatedMinimum_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    P {ω | ∃ r q : ℚ≥0,
      nonnegativeRationalTime r < nonnegativeRationalTime q ∧
      runningMinimum (hB.continuousPathMap hBmeasurable ω)
        (nonnegativeRationalTime q) =
        runningMinimum (hB.continuousPathMap hBmeasurable ω)
          (nonnegativeRationalTime r) ∧
      ∃ v, nonnegativeRationalTime r ≤ v ∧
        v ≤ nonnegativeRationalTime q ∧
        hB.continuousPathMap hBmeasurable ω v =
          runningMinimum (hB.continuousPathMap hBmeasurable ω)
            (nonnegativeRationalTime r)} = 0 := by
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
  have hUnion : P (⋃ r : ℚ≥0, ⋃ q : ℚ≥0, E r q) = 0 :=
    measure_iUnion_null fun r => measure_iUnion_null fun q => hEnull r q
  have hset :
      {ω | ∃ r q : ℚ≥0,
        nonnegativeRationalTime r < nonnegativeRationalTime q ∧
        runningMinimum (pathB ω) (nonnegativeRationalTime q) =
          runningMinimum (pathB ω) (nonnegativeRationalTime r) ∧
        ∃ v, nonnegativeRationalTime r ≤ v ∧
          v ≤ nonnegativeRationalTime q ∧
          pathB ω v = runningMinimum (pathB ω) (nonnegativeRationalTime r)} =
      ⋃ r : ℚ≥0, ⋃ q : ℚ≥0, E r q := by
    ext ω
    simp only [E, Set.mem_ofPred_eq, Set.mem_iUnion]
  exact hset ▸ hUnion

end ProbabilityTheory

end
