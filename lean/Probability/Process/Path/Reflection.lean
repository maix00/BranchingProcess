/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Continuous
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Reflection of a continuous path after a time

The public definition and theorems in this file are:

- `ProbabilityTheory.reflectAfter`: the path
  $R_t f(u)=f(u)$ for $u\le t$ and $R_t f(u)=2f(t)-f(u)$ for $t<u$.
- `ProbabilityTheory.reflectAfter_apply_le`: $R_t f(u)=f(u)$ for $u\le t$.
- `ProbabilityTheory.reflectAfter_apply_of_lt`: $R_t f(u)=2f(t)-f(u)$ for $t<u$.
- `ProbabilityTheory.reflectAfter_involutive`: $R_t(R_t f)=f$.
- `ProbabilityTheory.measurable_reflectAfter`: for fixed $t$, the map
  $f\mapsto R_t f$ on continuous paths is Borel measurable.
- `ProbabilityTheory.measurable_reflectAfter_pair`: the map
  $(f,t)\mapsto R_t f$ is Borel measurable.
- `ProbabilityTheory.continuous_reflectAfter_pair`: reflection depends
  continuously on both the path and the reflection time.
- `ProbabilityTheory.continuous_reflectAfter_time`: for a fixed path,
  reflection varies continuously with the reflection time.

This is the path transformation in Theorem 2.1 of S. J. Dilworth and
Duncan Wright, *A direct proof of the reflection principle for Brownian
motion*, Theory Stoch. Process. 21(37):2 (2016), 1--3. It supplies the
reflection step needed for the Lévy identity cited in Lemma 2.3 of Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485.
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- Reflect a continuous real path about its value at time `t` after `t`. -/
noncomputable def reflectAfter (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) : C(ℝ≥0, ℝ) := by
  classical
  refine ⟨fun u => if u ≤ t then f u else 2 * f t - f u, ?_⟩
  apply Continuous.if_le f.continuous
    (continuous_const.sub f.continuous) continuous_id continuous_const
  intro u hu
  change u = t at hu
  change f u = 2 * f t - f u
  subst u
  ring

/-- Reflection leaves the path unchanged through its reflection time. -/
theorem reflectAfter_apply_le (f : C(ℝ≥0, ℝ)) (t u : ℝ≥0) (hu : u ≤ t) :
    reflectAfter f t u = f u := by
  simp [reflectAfter, hu]

/-- After the reflection time, the path is reflected about `f t`. -/
theorem reflectAfter_apply_of_lt (f : C(ℝ≥0, ℝ)) (t u : ℝ≥0) (hu : t < u) :
    reflectAfter f t u = 2 * f t - f u := by
  simp [reflectAfter, not_le.mpr hu]

/-- Reflection at a fixed time is an involution on continuous paths. -/
theorem reflectAfter_involutive (t : ℝ≥0) :
    Function.Involutive (fun f : C(ℝ≥0, ℝ) => reflectAfter f t) := by
  intro f
  ext u
  by_cases hu : u ≤ t
  · rw [reflectAfter_apply_le _ _ _ hu,
      reflectAfter_apply_le _ _ _ hu]
  · have htu : t < u := lt_of_not_ge hu
    rw [reflectAfter_apply_of_lt _ _ _ htu,
      reflectAfter_apply_le _ _ _ le_rfl,
      reflectAfter_apply_of_lt _ _ _ htu]
    ring

/-- Reflection at a fixed time is a measurable transformation of
continuous-path space. -/
theorem measurable_reflectAfter (t : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) => reflectAfter f t) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro u
  by_cases hu : u ≤ t
  · simpa only [reflectAfter_apply_le _ _ _ hu] using
      (continuous_eval_const u).measurable
  · have htu : t < u := lt_of_not_ge hu
    have hcont : Continuous (fun f : C(ℝ≥0, ℝ) => 2 * f t - f u) := by
      fun_prop
    simpa only [reflectAfter_apply_of_lt _ _ _ htu] using hcont.measurable

/-- Reflection is jointly measurable in the path and reflection time. -/
theorem measurable_reflectAfter_pair :
    Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => reflectAfter p.1 p.2) := by
  classical
  rw [ContinuousMap.measurable_iff_eval]
  intro u
  have hfixed : Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 u) :=
    (continuous_eval_const u).measurable.comp measurable_fst
  have hvariable : Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2) :=
    continuous_eval.measurable
  have hsplit : MeasurableSet {p : C(ℝ≥0, ℝ) × ℝ≥0 | u ≤ p.2} :=
    measurableSet_le measurable_const measurable_snd
  have hreflect : Measurable
      (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => 2 * p.1 p.2 - p.1 u) :=
    (measurable_const.mul hvariable).sub hfixed
  change Measurable (fun p : C(ℝ≥0, ℝ) × ℝ≥0 =>
    if u ≤ p.2 then p.1 u else 2 * p.1 p.2 - p.1 u)
  exact Measurable.ite hsplit hfixed hreflect

/-- Reflection depends continuously on the path and the reflection time
in the compact-open topology on continuous paths. -/
theorem continuous_reflectAfter_pair :
    Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => reflectAfter p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hleft : Continuous (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 => p.1.1 p.2) := by
    fun_prop
  have hright : Continuous
      (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 =>
        2 * p.1.1 p.1.2 - p.1.1 p.2) := by
    fun_prop
  have hpiece : Continuous
      (fun p : (C(ℝ≥0, ℝ) × ℝ≥0) × ℝ≥0 =>
        if p.2 ≤ p.1.2 then p.1.1 p.2 else 2 * p.1.1 p.1.2 - p.1.1 p.2) := by
    apply Continuous.if_le hleft hright continuous_snd (continuous_snd.comp continuous_fst)
    intro p hp
    change p.2 = p.1.2 at hp
    rw [hp]
    ring
  exact hpiece

/-- For a fixed continuous path, reflection varies continuously with
the reflection time in the compact-open topology. -/
theorem continuous_reflectAfter_time (f : C(ℝ≥0, ℝ)) :
    Continuous (reflectAfter f) := by
  exact continuous_reflectAfter_pair.comp (continuous_const.prodMk continuous_id)

end ProbabilityTheory

end
