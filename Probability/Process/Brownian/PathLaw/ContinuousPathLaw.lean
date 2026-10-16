/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.ContinuousMap.FiniteDimensional
public import Probability.Process.Brownian.PathLaw.ContinuousModification
public import Probability.Process.Path.TimeGrid.NonnegativeRationals
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Laws of continuous Brownian paths

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_continuousPathMap_eq`:
  continuous versions of Brownian processes have the same law on
  $C([0,\infty),\mathbb R)$.
- `ProbabilityTheory.IsBrownianReal.measure_continuousPathMap_scale_eq`:
  the Brownian path law is invariant under $f(t)\mapsto c^{-1/2}f(ct)$
  for $c>0$.

The proof identifies finite-dimensional distributions on nonnegative
rational times, a countable dense subset. This path-law uniqueness is used
to formalize the Brownian scaling invariance cited by Erwin Bolthausen in
Lemma 2.2 of *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. Bolthausen cites Paul Lévy, *Processus
Stochastique et Mouvement Brownien* (Gauthier-Villars, Paris, 1945), p. 246,
for that invariance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ProbabilityTheory.BrownianReal
open scoped NNReal

namespace ProbabilityTheory

private theorem continuousPath_standardBorel :
    StandardBorelSpace C(ℝ≥0, ℝ) := by infer_instance

/-- Apply the Brownian time and amplitude scaling to a continuous path. -/
noncomputable def brownianPathScaling (c : ℝ≥0) :
    C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun f =>
  ⟨fun t => (√c)⁻¹ * f (c * t), by fun_prop⟩

/-- Brownian scaling is measurable on continuous path space. -/
theorem measurable_brownianPathScaling (c : ℝ≥0) :
    Measurable (brownianPathScaling c) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_const.mul (ContinuousMap.measurable_eval (c * t))

/-- Continuous versions of Brownian processes have the same path law. The
finite-dimensional laws agree at every finite family of nonnegative rational
times, which form a dense subset of the time axis. -/
theorem IsBrownianReal.measure_continuousPathMap_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B C : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hBmeasurable : ∀ t, Measurable (B t))
    (hCmeasurable : ∀ t, Measurable (C t)) :
    P.map (hB.continuousPathMap hBmeasurable) =
      P.map (hC.continuousPathMap hCmeasurable) := by
  classical
  haveI : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  letI := continuousPath_standardBorel
  apply ContinuousMap.measure_eq_of_map_finiteEvaluation_eq_of_denseRange
    nonnegativeRationalTime denseRange_nonnegativeRationalTime
  intro I
  letI : Fintype I := Fintype.ofFinite I
  let time : ℚ≥0 ↪ ℝ≥0 :=
    ⟨nonnegativeRationalTime, nonnegativeRationalTime_injective⟩
  let J := I.map time
  let e : I ≃ J := I.equivMap time
  let reindex : (J → ℝ) → (I → ℝ) := fun x i => x (e i)
  let eval : C(ℝ≥0, ℝ) → (I → ℝ) :=
    ContinuousMap.finiteEvaluation (fun q : I => nonnegativeRationalTime q)
  have hreindex : Measurable reindex := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (e i)
  have hlawB : HasLaw (fun ω => reindex (J.restrict (B · ω)))
      ((projectiveFamily J).map reindex) P := by
    exact (hasLaw_map hreindex.aemeasurable).comp
      (hB.toIsPreBrownianReal.hasLaw J)
  have hlawC : HasLaw (fun ω => reindex (J.restrict (C · ω)))
      ((projectiveFamily J).map reindex) P := by
    exact (hasLaw_map hreindex.aemeasurable).comp
      (hC.toIsPreBrownianReal.hasLaw J)
  have haeB : eval ∘ hB.continuousPathMap hBmeasurable =ᵐ[P]
      fun ω => reindex (J.restrict (B · ω)) := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable]
      with ω hω
    funext i
    change hB.continuousPathMap hBmeasurable ω
        (nonnegativeRationalTime i) = B ((e i : J) : ℝ≥0) ω
    rw [hω]
    rfl
  have haeC : eval ∘ hC.continuousPathMap hCmeasurable =ᵐ[P]
      fun ω => reindex (J.restrict (C · ω)) := by
    filter_upwards [hC.continuousPathMap_ae_eq hCmeasurable]
      with ω hω
    funext i
    change hC.continuousPathMap hCmeasurable ω
        (nonnegativeRationalTime i) = C ((e i : J) : ℝ≥0) ω
    rw [hω]
    rfl
  have hEvalB := hlawB.congr haeB
  have hEvalC := hlawC.congr haeC
  have hmapB :
      (P.map (hB.continuousPathMap hBmeasurable)).map eval =
        (projectiveFamily J).map reindex := by
    rw [Measure.map_map]
    · exact hEvalB.map_eq
    · exact (ContinuousMap.continuous_finiteEvaluation
        (fun q : I => nonnegativeRationalTime q)).measurable
    · exact hB.measurable_continuousPathMap hBmeasurable
  have hmapC :
      (P.map (hC.continuousPathMap hCmeasurable)).map eval =
        (projectiveFamily J).map reindex := by
    rw [Measure.map_map]
    · exact hEvalC.map_eq
    · exact (ContinuousMap.continuous_finiteEvaluation
        (fun q : I => nonnegativeRationalTime q)).measurable
    · exact hC.measurable_continuousPathMap hCmeasurable
  simpa [eval] using hmapB.trans hmapC.symm

/-- Brownian path measure is invariant under the scaling cited by
Paul Lévy, *Processus Stochastique et Mouvement Brownien* (1945), p. 246,
published by Gauthier-Villars, Paris, and used by Erwin Bolthausen in
Lemma 2.2 of *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*. -/
theorem IsBrownianReal.measure_continuousPathMap_scale_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {c : ℝ≥0} (hc : c ≠ 0) :
    P.map (brownianPathScaling c ∘ hB.continuousPathMap hBmeasurable) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let Bc : ℝ≥0 → Ω → ℝ := fun t ω => (√c)⁻¹ * B (c * t) ω
  have hBc : IsBrownianReal Bc P := hB.smul hc
  have hBcmeasurable (t : ℝ≥0) : Measurable (Bc t) :=
    measurable_const.mul (hBmeasurable (c * t))
  have hpathEq :
      brownianPathScaling c ∘ hB.continuousPathMap hBmeasurable =ᵐ[P]
        hBc.continuousPathMap hBcmeasurable := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hBc.continuousPathMap_ae_eq hBcmeasurable] with ω hω hωc
    ext t
    change (√c)⁻¹ * hB.continuousPathMap hBmeasurable ω (c * t) =
      hBc.continuousPathMap hBcmeasurable ω t
    rw [hω (c * t), hωc t]
  calc
    P.map (brownianPathScaling c ∘ hB.continuousPathMap hBmeasurable) =
        P.map (hBc.continuousPathMap hBcmeasurable) := Measure.map_congr hpathEq
    _ = P.map (hB.continuousPathMap hBmeasurable) :=
      hBc.measure_continuousPathMap_eq hB hBcmeasurable hBmeasurable

end ProbabilityTheory

end
