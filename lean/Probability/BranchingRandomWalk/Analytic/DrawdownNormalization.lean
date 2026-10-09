/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Analytic.DrawdownSlicing
public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Sequence.IID

import Mathlib.Tactic.FieldSimp

/-!
# Standard-deviation normalization for drawdown events

The finite-variance drawdown estimate is proved for centered increments with
second moment one. Dividing every increment by a positive standard deviation
transports both the drawdown event and its endpoint threshold to that setting.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

private theorem displacement_div_const (n : ℕ) (increment : ℕ → ℝ)
    (sigma : ℝ) :
    AdditivePath.displacement n (fun k => increment k / sigma) =
      AdditivePath.displacement n increment / sigma := by
  simp [AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]

/-- The no-large-drawdown event is measurable: it is a countable intersection
of inequalities between finite partial sums, together with one endpoint
inequality. -/
theorem measurableSet_noLargeDropEndpointBelowEvent
    (horizon : ℕ) (delta threshold : ℝ) :
    MeasurableSet (noLargeDropEndpointBelowEvent horizon delta threshold) := by
  rw [show noLargeDropEndpointBelowEvent horizon delta threshold =
      (⋂ i : ℕ, ⋂ j : ℕ,
        {increment : ℕ → ℝ | i ≤ j → j ≤ horizon →
          AdditivePath.displacement i increment -
            AdditivePath.displacement j increment ≤ delta}) ∩
      {increment : ℕ → ℝ |
        AdditivePath.displacement horizon increment ≤ threshold} by
    ext increment
    simp [noLargeDropEndpointBelowEvent]]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i ≤ j
    · by_cases hj : j ≤ horizon
      · have hdiff : Measurable
            (fun increment : ℕ → ℝ =>
              AdditivePath.displacement i increment -
                AdditivePath.displacement j increment) :=
          (RandomWalk.displacement_measurable i).sub
            (RandomWalk.displacement_measurable j)
        have hseteq :
            {increment : ℕ → ℝ | i ≤ j → j ≤ horizon →
              AdditivePath.displacement i increment -
                AdditivePath.displacement j increment ≤ delta} =
            {increment : ℕ → ℝ |
              AdditivePath.displacement i increment -
                AdditivePath.displacement j increment ≤ delta} := by
          ext increment
          simp [hij, hj]
        rw [hseteq]
        exact measurableSet_le hdiff measurable_const
      · simp [hij, hj]
    · simp [hij]
  · exact measurableSet_Iic.preimage
      (RandomWalk.displacement_measurable horizon)

/-- Pulling back a drawdown-and-endpoint event under coordinatewise division
by a positive standard deviation gives the same event with both thresholds
divided by that standard deviation. -/
theorem noLargeDropEndpointBelowEvent_preimage_div
    {sigma : ℝ} (hsigma : 0 < sigma) (horizon : ℕ)
    (delta threshold : ℝ) :
    (fun increment : ℕ → ℝ => fun k => increment k / sigma) ⁻¹'
        noLargeDropEndpointBelowEvent horizon (delta / sigma)
          (threshold / sigma) =
      noLargeDropEndpointBelowEvent horizon delta threshold := by
  ext increment
  simp only [Set.mem_preimage, noLargeDropEndpointBelowEvent,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hdrop, hendpoint⟩
    refine ⟨?_, ?_⟩
    · intro i j hij hj
      have h := hdrop i j hij hj
      rw [displacement_div_const, displacement_div_const] at h
      have hsub :
          AdditivePath.displacement i increment / sigma -
              AdditivePath.displacement j increment / sigma =
            (AdditivePath.displacement i increment -
              AdditivePath.displacement j increment) / sigma := by ring
      rw [hsub] at h
      rw [div_le_div_iff₀ hsigma hsigma] at h
      nlinarith [h]
    · have h := hendpoint
      rw [displacement_div_const] at h
      rw [div_le_div_iff₀ hsigma hsigma] at h
      nlinarith [h]
  · rintro ⟨hdrop, hendpoint⟩
    refine ⟨?_, ?_⟩
    · intro i j hij hj
      have h := hdrop i j hij hj
      have hsub :
          AdditivePath.displacement i increment / sigma -
              AdditivePath.displacement j increment / sigma =
          (AdditivePath.displacement i increment -
              AdditivePath.displacement j increment) / sigma := by ring
      rw [displacement_div_const, displacement_div_const]
      rw [hsub]
      rw [div_le_div_iff₀ hsigma hsigma]
      exact mul_le_mul_of_nonneg_right h hsigma.le
    · rw [displacement_div_const]
      rw [div_le_div_iff₀ hsigma hsigma]
      exact mul_le_mul_of_nonneg_right hendpoint hsigma.le

/-- Coordinatewise standard-deviation scaling transports the event measure
under the canonical i.i.d. sequence law. -/
theorem iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_eq_map_div
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hsigma : 0 < sigma) (horizon : ℕ) (delta threshold : ℝ) :
    iidSequenceLaw ν (noLargeDropEndpointBelowEvent horizon delta threshold) =
      iidSequenceLaw (ν.map fun x : ℝ => x / sigma)
        (noLargeDropEndpointBelowEvent horizon (delta / sigma)
          (threshold / sigma)) := by
  let scale : (ℕ → ℝ) → (ℕ → ℝ) := fun increment k => increment k / sigma
  have hscale : Measurable scale := by
    apply Measurable.of_eval
    intro k
    exact (measurable_id.div_const sigma).comp (measurable_pi_apply k)
  have htarget := measurableSet_noLargeDropEndpointBelowEvent horizon
    (delta / sigma) (threshold / sigma)
  have hmap := Measure.map_apply (μ := iidSequenceLaw ν) hscale htarget
  have hpreimage := noLargeDropEndpointBelowEvent_preimage_div
    hsigma horizon delta threshold
  change iidSequenceLaw ν
      (noLargeDropEndpointBelowEvent horizon delta threshold) = _
  calc
    iidSequenceLaw ν (noLargeDropEndpointBelowEvent horizon delta threshold) =
        iidSequenceLaw ν (scale ⁻¹'
          noLargeDropEndpointBelowEvent horizon (delta / sigma)
            (threshold / sigma)) := by rw [hpreimage]
    _ = (iidSequenceLaw ν).map scale
          (noLargeDropEndpointBelowEvent horizon (delta / sigma)
            (threshold / sigma)) := hmap.symm
    _ = iidSequenceLaw (ν.map fun x : ℝ => x / sigma)
          (noLargeDropEndpointBelowEvent horizon (delta / sigma)
            (threshold / sigma)) := by
      rw [show scale = fun increment : ℕ → ℝ => fun k => increment k / sigma by
        rfl]
      rw [iidSequenceLaw_map_coordinatewise ν (fun x => x / sigma)
        (measurable_id.div_const sigma)]

/-- The unit-variance Aïdékon--Hu drawdown estimate transports to any
centered increment law with positive finite variance. The rate is multiplied
by that variance because the normalized spatial scale is `delta / sigma`. -/
theorem eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {horizon : ℕ → ℕ} {delta : ℕ → ℝ}
    (c target blockTarget : ℝ) (hc : 0 < c)
    (htarget : 0 < target) (hblockTarget : target < blockTarget)
    (hblockTargetUpper : blockTarget < Real.pi ^ 2 / 2)
    (hdelta : Tendsto delta atTop atTop)
    (hratio : Tendsto (fun n => (horizon n : ℝ) / delta n ^ 2)
      atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (delta n / c)) ≤
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 * (horizon n : ℝ) / delta n ^ 2)) := by
  let νunit : Measure ℝ := ν.map fun x : ℝ => x / sigma
  let deltaUnit : ℕ → ℝ := fun n => delta n / sigma
  have hνunit : IsCenteredUnitSecondMoment νunit := by
    simpa [νunit] using hν.map_div hsigma
  change (∫ x : ℝ, x ∂νunit) = 0 ∧ (∫ x : ℝ, x ^ 2 ∂νunit) = 1 at hνunit
  rcases hνunit with ⟨hcentered, hsecondMoment⟩
  have hdeltaUnit : Tendsto deltaUnit atTop atTop := by
    dsimp [deltaUnit]
    simpa [div_eq_mul_inv, mul_comm] using
      hdelta.const_mul_atTop (inv_pos.mpr hsigma)
  have hratioScaled : Tendsto
      (fun n => sigma ^ 2 * ((horizon n : ℝ) / delta n ^ 2)) atTop atTop :=
    hratio.const_mul_atTop (sq_pos_of_pos hsigma)
  have hratioEq : (fun n =>
      (horizon n : ℝ) / (deltaUnit n) ^ 2) =ᶠ[atTop]
      fun n => sigma ^ 2 * ((horizon n : ℝ) / delta n ^ 2) := by
    filter_upwards [hdelta.eventually_gt_atTop 0] with n hδ
    have hδne : delta n ≠ 0 := ne_of_gt hδ
    have hσne : sigma ≠ 0 := ne_of_gt hsigma
    dsimp [deltaUnit]
    field_simp [hδne, hσne]
  have hratioUnit : Tendsto
      (fun n => (horizon n : ℝ) / (deltaUnit n) ^ 2) atTop atTop :=
    Filter.Tendsto.congr' hratioEq.symm hratioScaled
  have hunitBound :=
    eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp
      νunit hcentered hsecondMoment hB hcontinuous hmeasurable
      (delta := deltaUnit) c target blockTarget hc htarget hblockTarget
      hblockTargetUpper hdeltaUnit hratioUnit
  have hthresholdEq (n : ℕ) :
      deltaUnit n / c = (delta n / c) / sigma := by
    dsimp [deltaUnit]
    field_simp [hc.ne', hsigma.ne']
  have hmeasureEq (n : ℕ) :
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (delta n / c)) =
      iidSequenceLaw νunit (noLargeDropEndpointBelowEvent
        (horizon n) (deltaUnit n) (deltaUnit n / c)) := by
    rw [hthresholdEq n]
    exact iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_eq_map_div
      hsigma (horizon n) (delta n) (delta n / c)
  have hexponentEq (n : ℕ) (hδ : 0 < delta n) :
      -target * (horizon n : ℝ) / (deltaUnit n) ^ 2 =
        -target * sigma ^ 2 * (horizon n : ℝ) / delta n ^ 2 := by
    have hδne : delta n ≠ 0 := ne_of_gt hδ
    have hσne : sigma ≠ 0 := ne_of_gt hsigma
    dsimp [deltaUnit]
    field_simp [hδne, hσne]
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n :=
    hdelta.eventually_gt_atTop 0
  filter_upwards [hunitBound, hdeltaPos] with n hn hδ
  rw [hmeasureEq n]
  rw [hexponentEq n hδ] at hn
  exact hn

/-- Uniform-in-scale Aïdékon--Hu drawdown estimate for any centered
finite-variance increment law. The threshold condition
`horizon ≥ delta^(2+p)` with `p > 0` forces the diffusive ratio to infinity;
after standard-deviation normalization, the rate is multiplied by
`sigma^2`. -/
theorem exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (c target blockTarget p : ℝ) (hc : 0 < c)
    (htarget : 0 < target) (hblockTarget : target < blockTarget)
    (hblockTargetUpper : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, delta0 ≤ delta → ∀ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) →
          iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (delta / c)) ≤
            ENNReal.ofReal (Real.exp
              (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2)) := by
  by_contra hnoUniform
  have hbad : ∀ delta0 : ℝ, 0 < delta0 →
      ∃ delta : ℝ, delta0 ≤ delta ∧ ∃ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) ∧
          ¬ iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (delta / c)) ≤
              ENNReal.ofReal (Real.exp
                (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2)) := by
    intro delta0 hdelta0
    by_contra hnotBad
    apply hnoUniform
    refine ⟨delta0, hdelta0, ?_⟩
    intro delta hdelta horizon hlarge
    by_contra hnotBound
    exact hnotBad ⟨delta, hdelta, horizon, hlarge, hnotBound⟩
  have hbadNat : ∀ n : ℕ, ∃ delta : ℝ, (n : ℝ) ≤ delta ∧
      ∃ horizon : ℕ, delta ^ (2 + p) ≤ (horizon : ℝ) ∧
        ¬ iidSequenceLaw ν (noLargeDropEndpointBelowEvent
          horizon delta (delta / c)) ≤
            ENNReal.ofReal (Real.exp
              (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2)) := by
    intro n
    obtain ⟨delta, hdelta, horizon, hlarge, hbadBound⟩ :=
      hbad (max (n : ℝ) 1) (lt_of_lt_of_le (by norm_num)
        (le_max_right _ _))
    exact ⟨delta, le_trans (le_max_left _ _) hdelta,
      horizon, hlarge, hbadBound⟩
  choose delta hdeltaLower horizon hpower hbadBound using hbadNat
  have hdeltaTop : Tendsto delta atTop atTop :=
    tendsto_atTop_mono' atTop (Filter.Eventually.of_forall hdeltaLower)
      tendsto_natCast_atTop_atTop
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n :=
    hdeltaTop.eventually_gt_atTop 0
  have hratioLower : ∀ᶠ n : ℕ in atTop,
      delta n ^ p ≤ (horizon n : ℝ) / delta n ^ 2 := by
    filter_upwards [hdeltaPos] with n hδ
    have hpowerEq : delta n ^ (2 + p) = delta n ^ 2 * delta n ^ p := by
      calc
        delta n ^ (2 + p) = delta n ^ (2 : ℝ) * delta n ^ p :=
          Real.rpow_add hδ 2 p
        _ = delta n ^ 2 * delta n ^ p := by
          congr 1
          exact Real.rpow_natCast (delta n) 2
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
    calc
      delta n ^ p * delta n ^ 2 = delta n ^ 2 * delta n ^ p := by ring
      _ = delta n ^ (2 + p) := hpowerEq.symm
      _ ≤ (horizon n : ℝ) := hpower n
  have hdeltaPowerTop : Tendsto (fun n : ℕ => delta n ^ p) atTop atTop :=
    (_root_.tendsto_rpow_atTop hp).comp hdeltaTop
  have hratioTop : Tendsto (fun n : ℕ => (horizon n : ℝ) / delta n ^ 2)
      atTop atTop :=
    tendsto_atTop_mono' atTop hratioLower hdeltaPowerTop
  have hsequence :=
    eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp_of_centeredSecondMoment
      ν hν hsigma hB hcontinuous hmeasurable
      (horizon := horizon) (delta := delta)
      c target blockTarget hc htarget hblockTarget hblockTargetUpper
      hdeltaTop hratioTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsequence
  exact hbadBound N (hN N le_rfl)

end ProbabilityTheory.BranchingRandomWalk.Analytic

end
