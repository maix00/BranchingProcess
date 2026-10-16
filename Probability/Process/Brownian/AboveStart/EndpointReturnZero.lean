/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.AboveStart.EndpointReturn
public import Probability.Process.Brownian.Reflection.RandomLevelFirstPassage
public import Probability.Process.Path.FirstPassage.Restart

/-!
# Endpoint return of the first Brownian unit window

The public theorems in this file are:

- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_endpointReturn_eq_zero`:
  for a fixed horizon $s$, the first qualifying unit window has
  probability zero of ending at its starting level.
- `ProbabilityTheory.IsBrownianReal.measure_firstNonnegativeWindowStart_endpointReturn_eq_zero`:
  the same assertion for the unrestricted first window.

These are equation (2.2) of Lemma 2.3 in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. Bolthausen cites the Lévy decomposition
of descending hitting times to exclude a fixed excursion length.
Here that consequence is derived by conditioning at a rational time
inside the excursion and using the atomless first-passage law.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

private noncomputable def excursionGap (q : ℝ≥0)
    (f : C(ℝ≥0, ℝ)) : ℝ≥0 :=
  Real.toNNReal (f q - runningMinimum f q)

private noncomputable def excursionTarget (q : ℝ≥0)
    (f : C(ℝ≥0, ℝ)) : ℝ≥0 :=
  (firstPassageBelow f (runningMinimum f q)).untopA + 1 - q

private theorem measurable_excursionGap (q : ℝ≥0) :
    Measurable (excursionGap q) := by
  exact measurable_real_toNNReal.comp
    ((ContinuousMap.measurable_eval q).sub (measurable_runningMinimum q))

private theorem measurable_excursionTarget (q : ℝ≥0) :
    Measurable (excursionTarget q) := by
  have hpass : Measurable (fun f : C(ℝ≥0, ℝ) =>
      firstPassageBelow f (runningMinimum f q)) :=
    measurable_firstPassageBelow_pair.comp
      (measurable_id.prodMk (measurable_runningMinimum q))
  exact (hpass.untopA.add measurable_const).sub measurable_const

private theorem excursionGap_freezeAfter (f : C(ℝ≥0, ℝ)) (q : ℝ≥0) :
    excursionGap q (freezeAfter f q) = excursionGap q f := by
  unfold excursionGap
  rw [runningMinimum_freezeAfter_eq f (le_refl q)]
  simp [freezeAfter]

private theorem excursionTarget_freezeAfter (f : C(ℝ≥0, ℝ)) (q : ℝ≥0) :
    excursionTarget q (freezeAfter f q) = excursionTarget q f := by
  have hprefix (u : ℝ≥0) (hu : u ≤ q) :
      f u = (freezeAfter f q) u := by
    change f u = f (min u q)
    rw [min_eq_left hu]
  have hpassLe : firstPassageBelow f (runningMinimum f q) ≤ q :=
    (runningMinimum_le_iff_firstPassageBelow_le f q
      (runningMinimum f q)).mp le_rfl
  have hpass : firstPassageBelow (freezeAfter f q) (runningMinimum f q) =
      firstPassageBelow f (runningMinimum f q) :=
    (firstPassageBelow_eq_of_agreeOn f (freezeAfter f q)
      (runningMinimum f q) q hprefix hpassLe).symm
  simp [excursionTarget, runningMinimum_freezeAfter_eq f (le_refl q), hpass]

private theorem endpointReturn_rationalFuturePassage
    (f : C(ℝ≥0, ℝ)) (s t q : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s = t)
    (hend : f (t + 1) = f t)
    (hno : ¬ HasTripleRunningMinimumContact f)
    (htq : t < q) (hqd : q < t + 1) :
    0 < excursionGap q f ∧ 0 < excursionTarget q f ∧
      descendingHittingTime (shiftToZero f q) (excursionGap q f) =
        excursionTarget q f := by
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum f s t hfirst
  have hexc := firstNonnegativeWindowStartUpTo_endpointReturn_unitExcursion
    f s t hfirst hend hno
  have hqt : t + (q - t) = q := add_tsub_cancel_of_le htq.le
  have hqtPos : 0 < q - t := tsub_pos_iff_lt.mpr htq
  have hqtOne : q - t < 1 :=
    (tsub_lt_iff_left htq.le).2 (by simpa [add_comm] using hqd)
  have hminq : runningMinimum f q = f t := by
    rw [← hqt, runningMinimum_eq_of_between f hflat hqtOne.le, hrecord]
  have hgapReal : 0 < f q - runningMinimum f q := by
    have h := hexc.2.2 (q - t) hqtPos hqtOne
    rw [hqt] at h
    exact h
  have hgap : 0 < excursionGap q f := by
    exact Real.toNNReal_pos.mpr hgapReal
  have hfirstRecord : firstPassageBelow f (runningMinimum f q) = t := by
    rw [hminq]
    exact firstNonnegativeWindowStartUpTo_endpointReturn_firstPassageBelow
      f s t hfirst hend hno
  have htargetEq : excursionTarget q f = t + 1 - q := by
    unfold excursionTarget
    rw [hfirstRecord]
    rfl
  have htarget : 0 < excursionTarget q f := by
    rw [htargetEq]
    exact tsub_pos_iff_lt.mpr hqd
  have hstrict (u : ℝ≥0) (hqu : q ≤ u) (hud : u < t + 1) :
      runningMinimum f q < f u := by
    have htu : t < u := htq.trans_le hqu
    have htuEq : t + (u - t) = u := add_tsub_cancel_of_le htu.le
    have htuPos : 0 < u - t := tsub_pos_iff_lt.mpr htu
    have htuOne : u - t < 1 :=
      (tsub_lt_iff_left htu.le).2 (by simpa [add_comm] using hud)
    have h := hexc.2.2 (u - t) htuPos htuOne
    rw [htuEq] at h
    have hminu : runningMinimum f u = f t := by
      rw [← htuEq, runningMinimum_eq_of_between f hflat htuOne.le,
        hrecord]
    change 0 < f u - runningMinimum f u at h
    rw [hminu, ← hminq] at h
    exact sub_pos.mp h
  have hreturn : f (t + 1) ≤ runningMinimum f q := by
    rw [hend, hminq]
  have hpass := firstPassageBelow_shiftToZero_eq_of_strictUntil
    f (runningMinimum f q) hqd hreturn hstrict
  have hgapEq : -(excursionGap q f : ℝ) =
      runningMinimum f q - f q := by
    change -(Real.toNNReal (f q - runningMinimum f q) : ℝ) = _
    rw [Real.coe_toNNReal _ hgapReal.le]
    ring
  refine ⟨hgap, htarget, ?_⟩
  change firstPassageBelow (shiftToZero f q) (-(excursionGap q f : ℝ)) =
    (excursionTarget q f : WithTop ℝ≥0)
  rw [hgapEq, htargetEq]
  exact hpass

/-- Bolthausen's Lemma 2.3, equation (2.2), before a fixed horizon:
the first qualifying Brownian unit window almost surely has a strictly
higher endpoint. -/
theorem IsBrownianReal.measure_firstNonnegativeWindowStartUpTo_endpointReturn_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (s : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0,
      firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hBmeasurable ω) s = t ∧
      hB.continuousPathMap hBmeasurable ω (t + 1) =
        hB.continuousPathMap hBmeasurable ω t} = 0 := by
  let pathB := hB.continuousPathMap hBmeasurable
  let U : Set Ω := fun ω => HasTripleRunningMinimumContact (pathB ω)
  let A : ℚ≥0 → Set Ω := fun r =>
    let q := nonnegativeRationalTime r
    let past := fun ω => freezeAfter (pathB ω) q
    {ω | 0 < excursionGap q (past ω) ∧
      0 < excursionTarget q (past ω) ∧
      descendingHittingTime (shiftToZero (pathB ω) q)
        (excursionGap q (past ω)) = excursionTarget q (past ω)}
  have hUnull : P U = 0 :=
    hB.measure_tripleRunningMinimumContact_eq_zero hBmeasurable
  have hAnull (r : ℚ≥0) : P (A r) = 0 := by
    exact hB.measure_randomLevelFirstPassage_eq_zero
      hBmeasurable (nonnegativeRationalTime r)
      (excursionGap (nonnegativeRationalTime r))
      (excursionTarget (nonnegativeRationalTime r))
      (measurable_excursionGap _) (measurable_excursionTarget _)
  have hcover :
      {ω | ∃ t : ℝ≥0,
        firstNonnegativeWindowStartUpTo (pathB ω) s = t ∧
        pathB ω (t + 1) = pathB ω t} ⊆
        U ∪ ⋃ r : ℚ≥0, A r := by
    intro ω hω
    obtain ⟨t, hfirst, hend⟩ := hω
    by_cases hU : HasTripleRunningMinimumContact (pathB ω)
    · exact Set.mem_union_left _ hU
    · obtain ⟨r, htr, hrd⟩ := exists_nonnegativeRationalTime_between
        (lt_add_of_pos_right t (by norm_num : (0 : ℝ≥0) < 1))
      have hbridge := endpointReturn_rationalFuturePassage
        (pathB ω) s t (nonnegativeRationalTime r)
        hfirst hend hU htr hrd
      apply Set.mem_union_right
      apply Set.mem_iUnion.mpr
      refine ⟨r, ?_⟩
      simpa only [A, Set.mem_ofPred_eq, excursionGap_freezeAfter,
        excursionTarget_freezeAfter] using hbridge
  exact measure_mono_null hcover
    (measure_union_null hUnull (measure_iUnion_null hAnull))

/-- Bolthausen's Lemma 2.3, equation (2.2), for the unrestricted
first qualifying Brownian unit window. -/
theorem IsBrownianReal.measure_firstNonnegativeWindowStart_endpointReturn_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    P {ω | ∃ t : ℝ≥0,
      firstNonnegativeWindowStart
        (hB.continuousPathMap hBmeasurable ω) = t ∧
      hB.continuousPathMap hBmeasurable ω (t + 1) =
        hB.continuousPathMap hBmeasurable ω t} = 0 := by
  let pathB := hB.continuousPathMap hBmeasurable
  let E : ℕ → Set Ω := fun n =>
    {ω | ∃ t : ℝ≥0,
      firstNonnegativeWindowStartUpTo (pathB ω) n = t ∧
      pathB ω (t + 1) = pathB ω t}
  have hEnull (n : ℕ) : P (E n) = 0 :=
    hB.measure_firstNonnegativeWindowStartUpTo_endpointReturn_eq_zero
      hBmeasurable n
  have hcover :
      {ω | ∃ t : ℝ≥0,
        firstNonnegativeWindowStart (pathB ω) = t ∧
        pathB ω (t + 1) = pathB ω t} ⊆ ⋃ n : ℕ, E n := by
    intro ω hω
    obtain ⟨t, hfirst, hend⟩ := hω
    obtain ⟨n, hn⟩ := exists_nat_ge (t + 1)
    have hfirstn := firstNonnegativeWindowStartUpTo_eq_first_of_le
      (pathB ω) (s := n) hfirst hn
    exact Set.mem_iUnion.mpr ⟨n, ⟨t, hfirstn, hend⟩⟩
  exact measure_mono_null hcover (measure_iUnion_null hEnull)

end ProbabilityTheory

end
