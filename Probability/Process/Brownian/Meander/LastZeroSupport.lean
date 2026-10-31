/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Support.LinearPath
public import Probability.Process.Brownian.Meander.LastZeroLaw
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Measure.Support
import Topology.ContinuousMap.LastSignChange
import Topology.Order.UnitInterval.Time
public import Topology.Cadlag.Skorokhod.Maps.Continuous
public import Topology.Cadlag.Skorokhod.Path.Linear

/-!
# Linear paths in the support of the Brownian terminal excursion

## Public declarations

Writing $\mathcal M_B$ for the law of the normalized Brownian terminal
excursion and $\ell_a(t)=at$, every $a>0$ satisfies
$\ell_a\in\operatorname{supp}(\mathcal M_B)$; its image in Skorokhod space
belongs to the support of the pushed-forward law.

- `ProbabilityTheory.IsBrownianReal.linearPath_mem_lastZeroMeanderPathLaw_support`:
  every positive linear path belongs to the support of Iglehart's
  Brownian terminal-excursion law.
- `ProbabilityTheory.IsBrownianReal.linearPath_mem_lastZeroMeanderCadlagLaw_support`:
  the same support statement after embedding continuous paths in
  Skorokhod space.

The terminal-excursion representation is from Donald L. Iglehart,
*Functional Central Limit Theorems for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 2(4) (1974), 608--619, DOI 10.1214/aop/1176996607, Section 3, theorem (3.4), p. 616.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace ProbabilityTheory

/-- A positive linear path has no zero after time zero. -/
private lemma lastZero_linearPath {a : ℝ} (ha : 0 < a) :
    ContinuousMap.lastZero (ContinuousMap.linearPath a) = 0 := by
  have hset : {t : unitInterval | ContinuousMap.linearPath a t = 0} = {0} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, ContinuousMap.linearPath,
      ContinuousMap.coe_mk, mul_eq_zero]
    constructor
    · intro h
      rcases h with h | h
      · exact (ne_of_gt ha h).elim
      · exact Subtype.ext h
    · intro h
      subst t
      exact Or.inr rfl
  rw [ContinuousMap.lastZero, hset]
  simp

/-- Iglehart's terminal excursion transform fixes every positive linear
path on the unit interval. -/
private lemma lastZeroMeanderTransform_linearPath
    {a : ℝ} (ha : 0 < a) :
    ContinuousMap.lastZeroMeanderTransform (ContinuousMap.linearPath a) =
      ContinuousMap.linearPath a := by
  apply ContinuousMap.ext
  intro t
  have hzero := lastZero_linearPath ha
  have htime : unitInterval.terminalSegmentParameter (0 : unitInterval) t = t := by
    apply Subtype.ext
    change (0 : ℝ) + (1 - 0) * (t : ℝ) = (t : ℝ)
    ring
  have heval : ContinuousMap.lastZeroMeanderTransform
      (ContinuousMap.linearPath a) t =
      |(ContinuousMap.linearPath a) (unitInterval.terminalSegmentParameter 0 t)| /
        Real.sqrt (1 - (0 : ℝ)) := by
    have hne : (0 : unitInterval) ≠ ⊤ := ne_of_lt (by
      change (0 : ℝ) < 1
      norm_num)
    simp [ContinuousMap.lastZeroMeanderTransform, hzero, hne]
  rw [heval, htime]
  simp [ContinuousMap.linearPath, abs_of_nonneg (mul_nonneg ha.le t.property.1)]

/-- Positive linear paths lie in the support of Iglehart's normalized
Brownian terminal-excursion law. -/
theorem IsBrownianReal.linearPath_mem_lastZeroMeanderPathLaw_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : 0 < a) :
    ContinuousMap.linearPath a ∈
      (hB.lastZeroMeanderPathLaw hmeasurable).support := by
  let path : Ω → C(unitInterval, ℝ) := fun ω =>
    restrictPathToUnitInterval (hB.continuousPathMap hmeasurable ω)
  let transform : C(unitInterval, ℝ) → C(unitInterval, ℝ) :=
    ContinuousMap.lastZeroMeanderTransform
  have hpath : Measurable path :=
    continuous_restrictPathToUnitInterval.measurable.comp
      (hB.measurable_continuousPathMap hmeasurable)
  have hsource : ContinuousMap.linearPath a ∈ (P.map path).support :=
    hB.linearPath_mem_support hmeasurable a
  have hcont : ContinuousAt transform (ContinuousMap.linearPath a) :=
    ContinuousMap.continuousAt_lastZeroMeanderTransform_of_lastZero_eq_zero
      _ (lastZero_linearPath ha)
  apply (Measure.mem_support_iff_forall _).2
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hpre : transform ⁻¹' Metric.ball (ContinuousMap.linearPath a) r ∈
      𝓝 (ContinuousMap.linearPath a) := by
    have hballnhds : Metric.ball (transform (ContinuousMap.linearPath a)) r ∈
        𝓝 (transform (ContinuousMap.linearPath a)) :=
      Metric.ball_mem_nhds _ hr
    simpa only [Filter.mem_map, transform,
      lastZeroMeanderTransform_linearPath ha]
      using hcont hballnhds
  have hpos : 0 < (P.map path)
      (transform ⁻¹' Metric.ball (ContinuousMap.linearPath a) r) :=
    (Measure.mem_support_iff_forall _).1 hsource _ hpre
  have htarget : 0 < hB.lastZeroMeanderPathLaw hmeasurable
      (Metric.ball (ContinuousMap.linearPath a) r) := by
    rw [IsBrownianReal.lastZeroMeanderPathLaw,
      Measure.map_apply (hB.measurable_lastZeroMeanderPath hmeasurable)
        Metric.isOpen_ball.measurableSet]
    rw [Measure.map_apply hpath
      (ContinuousMap.measurable_lastZeroMeanderTransform
        Metric.isOpen_ball.measurableSet)] at hpos
    exact hpos
  exact htarget.trans_le (measure_mono hball)

/-- The same terminal-excursion support statement in the Skorokhod path
space used by the conditioned random-walk limit. -/
theorem IsBrownianReal.linearPath_mem_lastZeroMeanderCadlagLaw_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t))
    {a : ℝ} (ha : 0 < a) :
    Skorokhod.linearPath a ∈
      ((hB.lastZeroMeanderPathLaw hmeasurable).map
        Skorokhod.ofContinuousMap).support := by
  let emb : C(unitInterval, ℝ) → CadlagPath unitInterval ℝ :=
    Skorokhod.ofContinuousMap
  have hemb : emb (ContinuousMap.linearPath a) =
      Skorokhod.linearPath a := rfl
  have hsource : ContinuousMap.linearPath a ∈
      (hB.lastZeroMeanderPathLaw hmeasurable).support :=
    hB.linearPath_mem_lastZeroMeanderPathLaw_support
      hmeasurable ha
  apply (Measure.mem_support_iff_forall _).2
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hpre : emb ⁻¹' Metric.ball (Skorokhod.linearPath a) r ∈
      𝓝 (ContinuousMap.linearPath a) := by
    have hU' : Metric.ball (emb (ContinuousMap.linearPath a)) r ∈
        𝓝 (emb (ContinuousMap.linearPath a)) := Metric.ball_mem_nhds _ hr
    rw [hemb] at hU'
    exact Skorokhod.continuous_ofContinuousMap.continuousAt hU'
  have hpos := (Measure.mem_support_iff_forall _).1 hsource _ hpre
  have hballPos : 0 < ((hB.lastZeroMeanderPathLaw hmeasurable).map emb)
      (Metric.ball (Skorokhod.linearPath a) r) := by
    rw [Measure.map_apply Skorokhod.measurable_ofContinuousMap
      Metric.isOpen_ball.measurableSet]
    exact hpos
  exact hballPos.trans_le (measure_mono hball)

end ProbabilityTheory

end
