/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindowContinuity
public import Probability.Process.Brownian.AboveStart.FirstWindow
public import Probability.Process.Brownian.AboveStart.InteriorReturn
public import Probability.Process.Brownian.AboveStart.EndpointReturnZero
public import Probability.Process.Brownian.AboveStart.RunningMinimum

/-!
# Continuity of the first Brownian unit-window time

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_firstNonnegativeWindowStart`:
  the map $f\mapsto T(f)$ is continuous at almost every Brownian path.
- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_firstNonnegativeWindowStartUpTo_of_one_lt`:
  for $1<s<\infty$, the map $f\mapsto T^s(f)$ is continuous at
  almost every Brownian path.
- `ProbabilityTheory.IsBrownianReal.ae_continuousAt_firstNonnegativeWindowStartUpTo`:
  the same conclusion for every finite $s\ge0$.

This is the $s=\infty$ case of Erwin Bolthausen, *On a functional
central limit theorem for random walks conditioned to stay positive*,
Lemma 2.4, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. It uses equations (2.2) and (2.4)
of Lemma 2.3 and the almost-sure finiteness from Lemma 2.2.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- Bolthausen's Lemma 2.4 for the unrestricted first eligible
unit window: Brownian paths are almost surely continuity points of
the first-window-time functional. -/
theorem IsBrownianReal.ae_continuousAt_firstNonnegativeWindowStart
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    ∀ᵐ ω ∂P, ContinuousAt firstNonnegativeWindowStart
      (hB.continuousPathMap hBmeasurable ω) := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hfiniteMeas : MeasurableSet
      {ω | firstNonnegativeWindowStart (pathB ω) ≠ ⊤} := by
    exact (measurable_firstNonnegativeWindowStart.comp
      (hB.measurable_continuousPathMap hBmeasurable))
        (measurableSet_singleton (⊤ : WithTop ℝ≥0)).compl
  have hfinite : ∀ᵐ ω ∂P,
      firstNonnegativeWindowStart (pathB ω) ≠ ⊤ :=
    (mem_ae_iff_prob_eq_one hfiniteMeas).mpr
      (hB.measure_firstNonnegativeWindowStart_ne_top_eq_one hBmeasurable)
  have hnoInterior : ∀ᵐ ω ∂P,
      ¬ ∃ t u : ℝ≥0,
        firstNonnegativeWindowStart (pathB ω) = t ∧
        0 < u ∧ u < 1 ∧ pathB ω (t + u) = pathB ω t := by
    apply ae_iff.mpr
    simpa only [not_not] using
      hB.measure_firstNonnegativeWindowStart_interiorReturn_eq_zero
        hBmeasurable
  have hnoEndpoint : ∀ᵐ ω ∂P,
      ¬ ∃ t : ℝ≥0,
        firstNonnegativeWindowStart (pathB ω) = t ∧
        pathB ω (t + 1) = pathB ω t := by
    apply ae_iff.mpr
    simpa only [not_not] using
      hB.measure_firstNonnegativeWindowStart_endpointReturn_eq_zero
        hBmeasurable
  filter_upwards [hfinite, hnoInterior, hnoEndpoint] with ω hω hωI hωE
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hω
  have hfirst : firstNonnegativeWindowStart (pathB ω) = t := ht.symm
  have heligible := (firstNonnegativeWindowStart_eq_coe_iff
    (pathB ω) t).mp hfirst |>.1
  have hinterior : ∀ u : ℝ≥0, 0 < u → u < 1 →
      pathB ω t < pathB ω (t + u) := by
    intro u hu0 hu1
    have hle := heligible ⟨u, ⟨bot_le, hu1.le⟩⟩
    have hne : pathB ω (t + u) ≠ pathB ω t := by
      intro heq
      exact hωI ⟨t, u, hfirst, hu0, hu1, heq⟩
    exact lt_of_le_of_ne hle hne.symm
  have hendpoint : pathB ω t < pathB ω (t + 1) := by
    have hle := heligible ⟨1, ⟨bot_le, le_rfl⟩⟩
    have hne : pathB ω (t + 1) ≠ pathB ω t := by
      intro heq
      exact hωE ⟨t, hfirst, heq⟩
    exact lt_of_le_of_ne hle hne.symm
  exact continuousAt_firstNonnegativeWindowStart_of_strictWindow
    (pathB ω) t hfirst hinterior hendpoint

/-- Bolthausen's Lemma 2.4 for each fixed finite horizon $s>1$.
Equation (2.3) excludes the sole new cutoff point $s-1$. -/
theorem IsBrownianReal.ae_continuousAt_firstNonnegativeWindowStartUpTo_of_one_lt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {s : ℝ≥0} (hs : 1 < s) :
    ∀ᵐ ω ∂P, ContinuousAt
      (fun f => firstNonnegativeWindowStartUpTo f s)
      (hB.continuousPathMap hBmeasurable ω) := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hnoBoundary : ∀ᵐ ω ∂P,
      firstNonnegativeWindowStartUpTo (pathB ω) s ≠ s - 1 := by
    apply ae_iff.mpr
    simpa only [not_not] using
      hB.measure_firstNonnegativeWindowStartUpTo_eq_last
        hBmeasurable hs
  filter_upwards [hB.ae_continuousAt_firstNonnegativeWindowStart
    hBmeasurable, hnoBoundary] with ω hcont hboundary
  have hcut : firstNonnegativeWindowStart (pathB ω) ≠
      (s - 1 : WithTop ℝ≥0) := by
    intro heq
    have hsum : s - 1 + 1 = s := tsub_add_cancel_of_le hs.le
    have hfirst := firstNonnegativeWindowStartUpTo_eq_first_of_le
      (pathB ω) heq hsum.le
    exact hboundary (by simpa [WithTop.coe_sub] using hfirst)
  exact continuousAt_firstNonnegativeWindowStartUpTo_of_ne_cutoff
    (pathB ω) hs.le hcont hcut

/-- At the shortest possible horizon $s=1$, Brownian motion has a
strictly negative running minimum, so the cutoff $T=0$ is excluded
almost surely. -/
private theorem IsBrownianReal.ae_firstNonnegativeWindowStart_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) :
    ∀ᵐ ω ∂P,
      firstNonnegativeWindowStart
        (hB.continuousPathMap hBmeasurable ω) ≠ 0 := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hminMap : ∀ᵐ f ∂(P.map pathB),
      runningMinimum f 1 < 0 := by
    have hset : MeasurableSet
        {f : C(ℝ≥0, ℝ) | runningMinimum f 1 < 0} :=
      (measurable_runningMinimum 1) measurableSet_Iio
    exact (mem_ae_iff_prob_eq_one hset).mpr
      (hB.measure_runningMinimum_lt_zero hBmeasurable (by norm_num))
  have hmin : ∀ᵐ ω ∂P, runningMinimum (pathB ω) 1 < 0 :=
    ae_of_ae_map
      (hB.measurable_continuousPathMap hBmeasurable).aemeasurable hminMap
  have hzero : ∀ᵐ ω ∂P, pathB ω 0 = 0 := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hB.eval_zero_ae_eq_zero] with ω hpath hBzero
    rw [hpath 0, hBzero]
  filter_upwards [hmin, hzero] with ω hminω hzeroω hfirst
  have hfirst1 : firstNonnegativeWindowStartUpTo (pathB ω) 1 = 0 :=
    firstNonnegativeWindowStartUpTo_eq_first_of_le
      (pathB ω) hfirst (by norm_num)
  obtain ⟨hrecord, hflat⟩ :=
    firstNonnegativeWindowStartUpTo_runningMinimum
      (pathB ω) 1 0 hfirst1
  have hminZero : runningMinimum (pathB ω) 1 = 0 := by
    simpa [hzeroω] using hflat.trans hrecord.symm
  exact (not_lt_of_ge hminZero.ge) hminω

/-- Bolthausen's Lemma 2.4 for every finite horizon $s$. -/
theorem IsBrownianReal.ae_continuousAt_firstNonnegativeWindowStartUpTo
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ContinuousAt
      (fun f => firstNonnegativeWindowStartUpTo f s)
      (hB.continuousPathMap hBmeasurable ω) := by
  rcases lt_trichotomy s 1 with hs | hs | hs
  · have hconst : (fun f : C(ℝ≥0, ℝ) =>
        firstNonnegativeWindowStartUpTo f s) = fun _ => ⊤ := by
      funext f
      exact firstNonnegativeWindowStartUpTo_eq_top_of_lt_one f hs
    exact Filter.Eventually.of_forall fun ω => by
      rw [hconst]
      exact continuousAt_const
  · subst s
    filter_upwards [hB.ae_continuousAt_firstNonnegativeWindowStart
      hBmeasurable,
      hB.ae_firstNonnegativeWindowStart_ne_zero hBmeasurable]
      with ω hcont hcut
    exact continuousAt_firstNonnegativeWindowStartUpTo_of_ne_cutoff
      (hB.continuousPathMap hBmeasurable ω) (by norm_num)
      hcont (by simpa using hcut)
  · exact hB.ae_continuousAt_firstNonnegativeWindowStartUpTo_of_one_lt
      hBmeasurable hs

end ProbabilityTheory

end
