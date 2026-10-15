/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Independence.FirstPassage
public import Probability.Process.Path.DescendingHittingTimeRestart

/-!
# Increments of Brownian descending hitting times

The public theorems in this file are:

- `ProbabilityTheory.IsBrownianReal.indepFun_descendingHittingTime_increment`:
  for $x,y>0$, the increment $\tau_{x+y}-\tau_x$ is independent of
  $\tau_x$, where $\tau_z=\inf\{t:B_t\le-z\}$.
- `ProbabilityTheory.IsBrownianReal.measure_descendingHittingTime_increment_eq`:
  the same increment has the law of $\tau_y$.

The proof combines the first-passage strong Markov property with the
pathwise restart identity. This is the independent-increment step of
the Lévy decomposition invoked in Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned
to stay positive*, Lemma 2.3, equation (2.2),
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- A Brownian descending hitting-time increment is independent of
the preceding hitting time. -/
theorem IsBrownianReal.indepFun_descendingHittingTime_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    (fun ω => (((descendingHittingTime
        (hB.continuousPathMap hBmeasurable ω) (x + y)).untopA -
      (descendingHittingTime
        (hB.continuousPathMap hBmeasurable ω) x).untopA : ℝ≥0) :
      WithTop ℝ≥0)) ⟂ᵢ[P]
    (fun ω => descendingHittingTime
      (hB.continuousPathMap hBmeasurable ω) x) := by
  let pathB := hB.continuousPathMap hBmeasurable
  have hpathB : Measurable pathB := hB.measurable_continuousPathMap hBmeasurable
  have hdesc : ∀ᵐ ω ∂P, ∀ a : ℝ, ∃ t : ℝ≥0, pathB ω t < a :=
    ae_of_ae_map hpathB.aemeasurable
      (hB.ae_continuousPath_unboundedBelow hBmeasurable)
  have hfinite (z : ℝ≥0) :
      ∀ᵐ ω ∂P, descendingHittingTime (pathB ω) z ≠ ⊤ := by
    filter_upwards [hdesc] with ω hω
    intro htop
    obtain ⟨u, hu⟩ := hω (-(z : ℝ))
    have hnever := (firstPassageBelow_eq_top_iff
      (pathB ω) (-(z : ℝ))).mp htop u
    exact (not_lt_of_ge hu.le) hnever
  have hzero : ∀ᵐ ω ∂P, pathB ω 0 = 0 := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hB.eval_zero_ae_eq_zero] with ω hω hω0
    rw [hω 0]
    exact hω0
  let F : Ω → C(ℝ≥0, ℝ) := fun ω =>
    shiftToZero (pathB ω) (descendingHittingTime (pathB ω) x).untopA
  let G : Ω → C(ℝ≥0, ℝ) := fun ω =>
    freezeAfter (pathB ω) (descendingHittingTime (pathB ω) x).untopA
  have hInd : F ⟂ᵢ[P] G :=
    hB.indepFun_shiftToZero_freezeAfter_firstPassageBelow
      hBmeasurable (-(x : ℝ))
  have hcomp :
      (fun ω => descendingHittingTime (F ω) y) ⟂ᵢ[P]
        (fun ω => descendingHittingTime (G ω) x) := by
    simpa only [Function.comp_def] using
      hInd.comp (measurable_descendingHittingTime y)
        (measurable_descendingHittingTime x)
  have hfuture :
      (fun ω => descendingHittingTime (F ω) y) =ᵐ[P]
      (fun ω => (((descendingHittingTime (pathB ω) (x + y)).untopA -
        (descendingHittingTime (pathB ω) x).untopA : ℝ≥0) : WithTop ℝ≥0)) := by
    filter_upwards [hfinite x, hfinite (x + y), hzero]
      with ω hxfin hxyfin hω0
    obtain ⟨tx, htx⟩ := WithTop.ne_top_iff_exists.mp hxfin
    obtain ⟨txy, htxy⟩ := WithTop.ne_top_iff_exists.mp hxyfin
    have hstart : -(x : ℝ) < pathB ω 0 := by
      rw [hω0]
      exact neg_lt_zero.mpr (by exact_mod_cast hx)
    have hrestart := descendingHittingTime_shiftToZero_eq
      (pathB ω) x y hy hstart htx.symm htxy.symm
    have htxA : (descendingHittingTime (pathB ω) x).untopA = tx := by
      rw [← htx]
      rfl
    have htxyA : (descendingHittingTime (pathB ω) (x + y)).untopA = txy := by
      rw [← htxy]
      rfl
    change descendingHittingTime
      (shiftToZero (pathB ω) (descendingHittingTime (pathB ω) x).untopA) y =
      (((descendingHittingTime (pathB ω) (x + y)).untopA -
        (descendingHittingTime (pathB ω) x).untopA : ℝ≥0) : WithTop ℝ≥0)
    rw [htxA, htxyA]
    exact hrestart
  have hpast :
      (fun ω => descendingHittingTime (G ω) x) =ᵐ[P]
      (fun ω => descendingHittingTime (pathB ω) x) := by
    filter_upwards [hfinite x] with ω hxfin
    obtain ⟨tx, htx⟩ := WithTop.ne_top_iff_exists.mp hxfin
    have hfreeze := firstPassageBelow_freezeAfter_eq
      (pathB ω) (-(x : ℝ)) tx htx.symm
    change descendingHittingTime
      (freezeAfter (pathB ω) (descendingHittingTime (pathB ω) x).untopA) x =
        descendingHittingTime (pathB ω) x
    rw [← htx]
    exact hfreeze
  exact hcomp.congr hfuture hpast

/-- A Brownian descending hitting-time increment of level length `y`
has the same distribution as the hitting time of level `y`. -/
theorem IsBrownianReal.measure_descendingHittingTime_increment_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    P.map (fun ω => (((descendingHittingTime
        (hB.continuousPathMap hBmeasurable ω) (x + y)).untopA -
      (descendingHittingTime
        (hB.continuousPathMap hBmeasurable ω) x).untopA : ℝ≥0) :
      WithTop ℝ≥0)) =
    (P.map (hB.continuousPathMap hBmeasurable)).map
      (fun f => descendingHittingTime f y) := by
  let pathB := hB.continuousPathMap hBmeasurable
  let F : Ω → C(ℝ≥0, ℝ) := fun ω =>
    shiftToZero (pathB ω) (descendingHittingTime (pathB ω) x).untopA
  have hpathB : Measurable pathB := hB.measurable_continuousPathMap hBmeasurable
  have hF : Measurable F :=
    measurable_shiftToZero.comp
      (hpathB.prodMk
        (((measurable_descendingHittingTime x).comp hpathB).untopA))
  have hdesc : ∀ᵐ ω ∂P, ∀ a : ℝ, ∃ t : ℝ≥0, pathB ω t < a :=
    ae_of_ae_map hpathB.aemeasurable
      (hB.ae_continuousPath_unboundedBelow hBmeasurable)
  have hfinite (z : ℝ≥0) :
      ∀ᵐ ω ∂P, descendingHittingTime (pathB ω) z ≠ ⊤ := by
    filter_upwards [hdesc] with ω hω
    intro htop
    obtain ⟨u, hu⟩ := hω (-(z : ℝ))
    have hnever := (firstPassageBelow_eq_top_iff
      (pathB ω) (-(z : ℝ))).mp htop u
    exact (not_lt_of_ge hu.le) hnever
  have hzero : ∀ᵐ ω ∂P, pathB ω 0 = 0 := by
    filter_upwards [hB.continuousPathMap_ae_eq hBmeasurable,
      hB.eval_zero_ae_eq_zero] with ω hω hω0
    rw [hω 0]
    exact hω0
  have hfuture :
      (fun ω => descendingHittingTime (F ω) y) =ᵐ[P]
      (fun ω => (((descendingHittingTime (pathB ω) (x + y)).untopA -
        (descendingHittingTime (pathB ω) x).untopA : ℝ≥0) : WithTop ℝ≥0)) := by
    filter_upwards [hfinite x, hfinite (x + y), hzero]
      with ω hxfin hxyfin hω0
    obtain ⟨tx, htx⟩ := WithTop.ne_top_iff_exists.mp hxfin
    obtain ⟨txy, htxy⟩ := WithTop.ne_top_iff_exists.mp hxyfin
    have hstart : -(x : ℝ) < pathB ω 0 := by
      rw [hω0]
      exact neg_lt_zero.mpr (by exact_mod_cast hx)
    have hrestart := descendingHittingTime_shiftToZero_eq
      (pathB ω) x y hy hstart htx.symm htxy.symm
    have htxA : (descendingHittingTime (pathB ω) x).untopA = tx := by
      rw [← htx]
      rfl
    have htxyA : (descendingHittingTime (pathB ω) (x + y)).untopA = txy := by
      rw [← htxy]
      rfl
    change descendingHittingTime
      (shiftToZero (pathB ω) (descendingHittingTime (pathB ω) x).untopA) y =
      (((descendingHittingTime (pathB ω) (x + y)).untopA -
        (descendingHittingTime (pathB ω) x).untopA : ℝ≥0) : WithTop ℝ≥0)
    rw [htxA, htxyA]
    exact hrestart
  have hshift : P.map F = P.map pathB := by
    have h := hB.measure_shiftToZero_firstPassageBelow_eq
      hBmeasurable (-(x : ℝ))
    have hshiftMeas : Measurable (fun f : C(ℝ≥0, ℝ) =>
        shiftToZero f (firstPassageBelow f (-(x : ℝ))).untopA) :=
      measurable_shiftToZero.comp
        (measurable_id.prodMk (measurable_firstPassageBelow _).untopA)
    calc
      P.map F = (P.map pathB).map
          (fun f => shiftToZero f (firstPassageBelow f (-(x : ℝ))).untopA) := by
        exact (Measure.map_map hshiftMeas hpathB).symm
      _ = P.map pathB := h
  calc
    P.map (fun ω => (((descendingHittingTime (pathB ω) (x + y)).untopA -
        (descendingHittingTime (pathB ω) x).untopA : ℝ≥0) : WithTop ℝ≥0)) =
        P.map (fun ω => descendingHittingTime (F ω) y) :=
      Measure.map_congr hfuture.symm
    _ = (P.map F).map (fun f => descendingHittingTime f y) :=
      (Measure.map_map (measurable_descendingHittingTime y) hF).symm
    _ = (P.map pathB).map (fun f => descendingHittingTime f y) := by rw [hshift]

end ProbabilityTheory

end
