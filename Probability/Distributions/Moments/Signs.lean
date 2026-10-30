/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Real

import Mathlib.MeasureTheory.Measure.Support

public section

/-!
# Two-sided increments under centered second-moment assumptions

A centered finite measure with nonzero second moment must charge both open
half-lines. These facts are the measure-theoretic input for constructing a
subexponential entrance path from either boundary of a corridor.

## Public declarations

- `ProbabilityTheory.IsCenteredUnitSecondMoment.measure_Iio_zero_pos`:
  if $\nu$ is finite, centered with unit second moment, then $0<\nu((-∞,0))$.
- `ProbabilityTheory.IsCenteredUnitSecondMoment.measure_Ioi_zero_pos`:
  under the same assumptions, $0<\nu((0,\infty))$.
- `ProbabilityTheory.IsCenteredSecondMoment.measure_Ioi_zero_pos`:
  if $\nu$ is finite and centered with second moment $\sigma^2>0$, then
  $0<\nu((0,\infty))$.
- `ProbabilityTheory.IsCenteredSecondMoment.measure_Iio_zero_pos`:
  under the same assumptions, $0<\nu((-∞,0))$.
- `ProbabilityTheory.IsCenteredUnitSecondMoment.exists_neg_interval_measure_pos`:
  there are $a<b<0$ with $\nu((a,b))>0$.
- `ProbabilityTheory.IsCenteredUnitSecondMoment.exists_pos_interval_measure_pos`:
  there are $0<a<b$ with $\nu((a,b))>0$.
- `ProbabilityTheory.IsCenteredSecondMoment.exists_neg_interval_measure_pos`:
  under the positive-variance assumptions, there are $a<b<0$ with
  $\nu((a,b))>0$.
- `ProbabilityTheory.IsCenteredSecondMoment.exists_pos_interval_measure_pos`:
  under the positive-variance assumptions, there are $0<a<b$ with
  $\nu((a,b))>0$.
- `ProbabilityTheory.IsCenteredSecondMoment.exists_pos_Icc_measure_pos`:
  for a centered finite measure with second moment $\sigma^2>0$, there are
  $0<a<b$ with $\nu([a,b])>0$.
- `ProbabilityTheory.IsCenteredSecondMoment.exists_reflected_pos_Icc_measure_pos`:
  its reflected measure also charges some bounded interval $[a,b]$ with
  $0<a<b$.

The closed-window conclusions are the increment-window input used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Appendix A.2, Lemma A.7, in the proof of
Chapter 3, Lemma 3.5.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

/-- A finite measure with zero mean and unit second moment assigns positive mass to negative
increments. -/
theorem IsCenteredUnitSecondMoment.measure_Iio_zero_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    0 < ν (Iio 0) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hnonneg : ∀ᵐ x : ℝ ∂ν, 0 ≤ x := by
    apply (ae_iff).2
    have hset : {x : ℝ | ¬0 ≤ x} = Iio 0 := by
      ext x
      simp
    rw [hset]
    exact hzero
  have hintegrable : Integrable (fun x : ℝ => x) ν := by
    change Integrable id ν
    exact hν.memLp_two.integrable (by norm_num)
  have hzeroAe : (fun x : ℝ => x) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hintegrable).1 hν.1
  have hsquareZero : (fun x : ℝ => x ^ 2) =ᵐ[ν] 0 :=
    hzeroAe.mono fun x hx => by simp [hx]
  have hsquareIntegral : (∫ x : ℝ, x ^ 2 ∂ν) = 0 :=
    integral_eq_zero_of_ae hsquareZero
  linarith [hν.2]

/-- A finite measure with zero mean and unit second moment assigns positive mass to positive
increments. -/
theorem IsCenteredUnitSecondMoment.measure_Ioi_zero_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    0 < ν (Ioi 0) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hnonpos : ∀ᵐ x : ℝ ∂ν, x ≤ 0 := by
    apply (ae_iff).2
    have hset : {x : ℝ | ¬x ≤ 0} = Ioi 0 := by
      ext x
      simp
    rw [hset]
    exact hzero
  have hintegrable : Integrable (fun x : ℝ => -x) ν := by
    change Integrable (-id) ν
    exact (hν.memLp_two.integrable (by norm_num)).neg
  have hnonneg : ∀ᵐ x : ℝ ∂ν, 0 ≤ -x :=
    hnonpos.mono fun _ hx => neg_nonneg.mpr hx
  have hintegral : (∫ x : ℝ, -x ∂ν) = 0 := by
    rw [integral_neg, hν.1, neg_zero]
  have hzeroAe : (fun x : ℝ => -x) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hintegrable).1 hintegral
  have hsquareZero : (fun x : ℝ => x ^ 2) =ᵐ[ν] 0 :=
    hzeroAe.mono fun x hx => by
      have : x = 0 := neg_eq_zero.mp hx
      simp [this]
  have hsquareIntegral : (∫ x : ℝ, x ^ 2 ∂ν) = 0 :=
    integral_eq_zero_of_ae hsquareZero
  linarith [hν.2]

/-- A finite measure with zero mean and positive second moment charges the positive half-line.
Divide by its positive second-moment scale and apply the unit-second-moment sign theorem. -/
theorem IsCenteredSecondMoment.measure_Ioi_zero_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    0 < ν (Ioi 0) := by
  have hunit := (hν.map_div hsigma).measure_Ioi_zero_pos
  have hmeas : Measurable (fun x : ℝ => x / sigma) := by fun_prop
  rw [Measure.map_apply hmeas measurableSet_Ioi] at hunit
  have hpreimage :
      (fun x : ℝ => x / sigma) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp [div_pos_iff_of_pos_right hsigma]
  rwa [hpreimage] at hunit

/-- A finite measure with zero mean and positive second moment charges the negative half-line. -/
theorem IsCenteredSecondMoment.measure_Iio_zero_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    0 < ν (Iio 0) := by
  have hunit := (hν.map_div hsigma).measure_Iio_zero_pos
  have hmeas : Measurable (fun x : ℝ => x / sigma) := by fun_prop
  rw [Measure.map_apply hmeas measurableSet_Iio] at hunit
  have hpreimage :
      (fun x : ℝ => x / sigma) ⁻¹' Iio 0 = Iio 0 := by
    ext x
    change x / sigma < 0 ↔ x < 0
    rw [div_lt_iff₀ hsigma]
    simp
  rwa [hpreimage] at hunit

/-- Some bounded open interval of strictly negative increments has positive
mass.  In particular, the increments in this event are bounded away from
both zero and minus infinity. -/
theorem IsCenteredUnitSecondMoment.exists_neg_interval_measure_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    ∃ lower upper : ℝ,
      lower < upper ∧ upper < 0 ∧ 0 < ν (Ioo lower upper) := by
  obtain ⟨x, hx, hxsupport⟩ :=
    ν.nonempty_inter_support_of_pos hν.measure_Iio_zero_pos
  have hxneg : x < 0 := hx
  let radius := -x / 2
  have hradius : 0 < radius := by dsimp [radius]; linarith
  refine ⟨x - radius, x + radius, by linarith, ?_, ?_⟩
  · dsimp [radius]
    linarith
  · apply (Measure.mem_support_iff_forall x).1 hxsupport
    exact Ioo_mem_nhds (by linarith) (by linarith)

/-- Some bounded open interval of strictly positive increments has positive
mass. -/
theorem IsCenteredUnitSecondMoment.exists_pos_interval_measure_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν) :
    ∃ lower upper : ℝ,
      0 < lower ∧ lower < upper ∧ 0 < ν (Ioo lower upper) := by
  obtain ⟨x, hx, hxsupport⟩ :=
    ν.nonempty_inter_support_of_pos hν.measure_Ioi_zero_pos
  have hxpos : 0 < x := hx
  let radius := x / 2
  have hradius : 0 < radius := by dsimp [radius]; linarith
  refine ⟨x - radius, x + radius, ?_, by linarith, ?_⟩
  · dsimp [radius]
    linarith
  · apply (Measure.mem_support_iff_forall x).1 hxsupport
    exact Ioo_mem_nhds (by linarith) (by linarith)

/-- A centered finite measure with positive second moment charges a bounded
negative increment window. -/
theorem IsCenteredSecondMoment.exists_neg_interval_measure_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    ∃ lower upper : ℝ,
      lower < upper ∧ upper < 0 ∧ 0 < ν (Ioo lower upper) := by
  obtain ⟨x, hx, hxsupport⟩ :=
    ν.nonempty_inter_support_of_pos (hν.measure_Iio_zero_pos hsigma)
  have hxneg : x < 0 := hx
  let radius := -x / 2
  refine ⟨x - radius, x + radius, by dsimp [radius]; linarith, ?_, ?_⟩
  · dsimp [radius]
    linarith
  · apply (Measure.mem_support_iff_forall x).1 hxsupport
    exact Ioo_mem_nhds (by dsimp [radius]; linarith)
      (by dsimp [radius]; linarith)

/-- A centered finite measure with positive second moment charges a bounded
positive increment window. -/
theorem IsCenteredSecondMoment.exists_pos_interval_measure_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    ∃ lower upper : ℝ,
      0 < lower ∧ lower < upper ∧ 0 < ν (Ioo lower upper) := by
  obtain ⟨x, hx, hxsupport⟩ :=
    ν.nonempty_inter_support_of_pos (hν.measure_Ioi_zero_pos hsigma)
  have hxpos : 0 < x := hx
  let radius := x / 2
  refine ⟨x - radius, x + radius, ?_, by dsimp [radius]; linarith, ?_⟩
  · dsimp [radius]
    linarith
  · apply (Measure.mem_support_iff_forall x).1 hxsupport
    exact Ioo_mem_nhds (by dsimp [radius]; linarith)
      (by dsimp [radius]; linarith)

/-! ## Closed bounded positive windows -/

/-- A centered finite measure with positive second moment charges a bounded closed interval of strictly
positive increments. -/
theorem IsCenteredSecondMoment.exists_pos_Icc_measure_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ 0 < ν (Set.Icc a b) := by
  obtain ⟨a, b, ha, hab, hmass⟩ := hν.exists_pos_interval_measure_pos hsigma
  refine ⟨a, b, ha, hab, hmass.trans_le ?_⟩
  exact measure_mono Set.Ioo_subset_Icc_self

/-- The reflected measure of a centered finite measure with positive second moment charges a bounded closed
interval of strictly positive reflected increments. -/
theorem IsCenteredSecondMoment.exists_reflected_pos_Icc_measure_pos
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      0 < (ν.map fun x : ℝ => -x) (Set.Icc a b) := by
  obtain ⟨lower, upper, hlt, hneg, hmass⟩ :=
    hν.exists_neg_interval_measure_pos hsigma
  refine ⟨-upper, -lower, by linarith, by linarith, ?_⟩
  rw [Measure.map_apply measurable_neg measurableSet_Icc]
  exact hmass.trans_le (measure_mono (by
    intro x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩))

end ProbabilityTheory
