/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.ContinuousPathLaw
public import Probability.Process.Path.Independence.DenseEvaluation
public import Probability.Process.Path.Continuous
public import Probability.Process.Brownian.Reflection.FirstPassagePrinciple
public import Probability.Independence.AtomlessEquality

/-!
# Brownian path independence across a deterministic time

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.indepFun_shiftPath_freezePath`:
  the path $u\mapsto B(r+u)-B(r)$ is independent of the frozen past path
  $u\mapsto B(\min(u,r))$.
- `ProbabilityTheory.IsBrownianReal.measure_pastMinimumGap_eq_futureMinimum`:
  for $d>0$, the probability that $m(r)-B(r)$ equals the minimum of
  $B(r+u)-B(r)$ over $0\le u\le d$ is zero.

This is the path-valued form of the weak Markov property in mathlib's
`IsPreBrownianReal.indepFun_shift`. It supplies the independence used
for the rational-interval event in Lemma 2.3 of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Ann. Probab. 4(3) (1976), 480--485,
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

end ProbabilityTheory

end
