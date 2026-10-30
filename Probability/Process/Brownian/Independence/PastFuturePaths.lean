/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Transform.Continuous

public import Probability.Process.Brownian.PathLaw.ContinuousModification
public import Probability.Process.Path.Representation.Continuous
import Probability.Process.Brownian.PathLaw.ContinuousPathLaw
import Probability.Process.Path.Independence.DenseEvaluation
import Topology.Order.NNReal.Rational

/-!
# Brownian path independence across a deterministic time

## Public declarations

- `ProbabilityTheory.IsBrownianReal.indepFun_shiftPath_freezePath`:
  the path $u\mapsto B(r+u)-B(r)$ is independent of the frozen past path
  $u\mapsto B(\min(u,r))$.
- `ProbabilityTheory.IsBrownianReal.indepFun_shiftToZero_freezeAfter`:
  the same independence expressed directly through the continuous
  Brownian path map.
- `ProbabilityTheory.IsBrownianReal.measure_shiftToZero_eq`:
  the future increment path at a fixed time has the original Brownian
  path law.

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
    fun x q => x ((q : ℝ≥0))
  have hEval : Measurable evaluate := by
    rw [measurable_pi_iff]
    intro q
    exact measurable_pi_apply ((q : ℝ≥0))
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
      ContinuousMap.finiteEvaluation (fun q : ℚ≥0 => (q : ℝ≥0)) ∘ futurePath := by
    filter_upwards [hshift.continuousPathMap_ae_eq hshiftMeas] with ω hω
    funext q
    exact (hω ((q : ℝ≥0))).symm
  have hPastAE : evaluate ∘ rawPast =ᵐ[P]
      ContinuousMap.finiteEvaluation (fun q : ℚ≥0 => (q : ℝ≥0)) ∘ pastPath := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable] with ω hω
    funext q
    exact (hω (min ((q : ℝ≥0)) r)).symm
  have hPathEvalInd := hEvalInd.congr hFutureAE hPastAE
  exact IndepFun.of_indep_finiteEvaluation
    (fun q : ℚ≥0 => (q : ℝ≥0)) NNRat.denseRange_cast_nnreal
    (fun q : ℚ≥0 => (q : ℝ≥0)) NNRat.denseRange_cast_nnreal hPathEvalInd

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


end ProbabilityTheory

end
