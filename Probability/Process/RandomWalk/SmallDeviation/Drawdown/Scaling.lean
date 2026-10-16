/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Sequence.IID.Basic

import Mathlib.Tactic.FieldSimp

/-!
# Scaling identities for drawdown events

Write
$B_{L,\Delta,r}=\{\xi:S_i-S_j\le\Delta\ (0\le i\le j\le L),\ S_L\le r\}$
for the drawdown endpoint event. The public theorems are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measurableSet_noLargeDropEndpointBelowEvent`: $B_{L,\Delta,r}$ is measurable.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent_preimage_div`: for $\sigma>0$ and
  $D_\sigma(\xi)_i=\xi_i/\sigma$,
  $D_\sigma^{-1}(B_{L,\Delta/\sigma,r/\sigma})=B_{L,\Delta,r}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_eq_map_div`:
  $\mathbb P_\nu(B_{L,\Delta,r})=
  \mathbb P_{\nu\circ(x\mapsto x/\sigma)^{-1}}
  (B_{L,\Delta/\sigma,r/\sigma})$.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

private lemma displacement_div_const (n : ℕ) (increment : ℕ → ℝ)
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
