/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance
public import Probability.Distributions.Moments.Real
public import Analysis.Asymptotics.Scale.Block.Diffusive
public import Probability.Process.RandomWalk.Path.Block.Basic
public import Probability.Sequence.IID.Basic

import Probability.Process.RandomWalk.Path.Block.Corridor.Core
import Probability.Process.RandomWalk.Path.Block.Maximal.SecondMoment

/-!
# Second-moment bound for block corridors

Let \(X_j\) be IID increments with law \(\nu\), let
\(S_k=\sum_{j<k}X_j\), and write
\(\mathbb P_\nu=\operatorname{iidSequenceLaw}(\nu)\). Assume \(X_j\) has mean
zero and finite second moment. For every block start \(s\), length \(\ell\),
corridor \([a,b]\), and margin \(r>0\), the public theorem gives
\[
  \mathbb P_\nu\bigl(
    a+r\leq S_s\leq b-r
  \bigr)
  \leq
  \mathbb P_\nu\bigl(
    S_{s+k}\in[a,b]\text{ for every }0\leq k\leq\ell
  \bigr)
  +\operatorname{ofReal}\!\left(\frac{(\ell+1)\operatorname{Var}_\nu(X_1)}{r^2}\right).
\]

## Main result

- `measure_startMargin_le_blockCorridor_add_of_centeredFiniteVariance`:
  starting in the radius-`r` interior of `[a,b]` has probability at most the
  probability of staying in `[a,b]` throughout the block, plus
  `ofReal ((length + 1) * variance id ν / radius^2)`.

The proof composes the distribution-free block-corridor inclusion with the
centered finite-second-moment maximal inequality.

## Public declarations

* `measure_startMargin_le_blockCorridor_add_of_centeredFiniteVariance` gives
  the bound
  `iidSequenceLaw ν {ω | lower + radius ≤ AdditivePath.displacement start ω ∧
  AdditivePath.displacement start ω ≤ upper - radius} ≤
  iidSequenceLaw ν {ω | ∀ k ≤ length,
  AdditivePath.displacement (start + k) ω ∈ Set.Icc lower upper} +
  ENNReal.ofReal (((length + 1 : ℝ) * variance id ν) / radius ^ 2)` for
  centered square-integrable IID increments and `radius > 0`.
* `exists_diffusiveBlockConstant_eventually_startMargin_le_corridor_add`:
  for unit-second-moment increments and any spatial scale tending to infinity,
  some diffusive block constant makes the same margin-to-corridor comparison
  hold eventually and uniformly over deterministic starts and corridor
  endpoints, with any prescribed positive additive error.
-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Under centered square-integrable IID increments, the probability of
starting inside a corridor margin is bounded by the probability of staying
inside the corridor for the whole block, plus the explicit maximal-inequality
error. -/
theorem measure_startMargin_le_blockCorridor_add_of_centeredFiniteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmem : MemLp id 2 ν) (hcentered : ∫ x, x ∂ν = 0)
    {lower upper radius : ℝ} (hradius : 0 < radius)
    (start length : ℕ) :
    (iidSequenceLaw ν) {increment |
        lower + radius ≤ AdditivePath.displacement start increment ∧
          AdditivePath.displacement start increment ≤ upper - radius} ≤
      (iidSequenceLaw ν) {increment | ∀ k ≤ length,
          AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
        ENNReal.ofReal (((length + 1 : ℝ) * variance id ν) / radius ^ 2) := by
  have hlarge :
      (iidSequenceLaw ν) {increment |
        ∃ k ∈ Finset.range (length + 1),
          radius ≤ |AdditivePath.blockSum start (k + 1) increment|} ≤
        ENNReal.ofReal (((length + 1 : ℝ) * variance id ν) / radius ^ 2) := by
    let ε : ℝ≥0 := ⟨radius ^ 2, sq_nonneg radius⟩
    have hmax := maximal_ineq_sq_blockSum_iidSequenceLaw
      ν hmem hcentered start ε length
    have hevent :
        {path : ℕ → ℝ | radius ^ 2 ≤
          (Finset.range (length + 1)).sup' Finset.nonempty_range_add_one
            fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} =
        {path | ∃ k ∈ Finset.range (length + 1),
          radius ≤ |AdditivePath.blockSum start (k + 1) path|} := by
      ext path
      simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
      constructor
      · rintro ⟨k, hk, hkbound⟩
        exact ⟨k, hk, by
          rw [← abs_of_pos hradius, ← sq_le_sq]
          exact hkbound⟩
      · rintro ⟨k, hk, hkbound⟩
        exact ⟨k, hk, by
          rw [sq_le_sq, abs_of_pos hradius]
          exact hkbound⟩
    rw [← hevent, ENNReal.ofReal_div_of_pos (sq_pos_of_pos hradius)]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hradius)).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2
    rw [mul_comm]
    have hε : (ε : ENNReal) = ENNReal.ofReal (radius ^ 2) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl
    rw [← hε]
    change (ε : ENNReal) * (iidSequenceLaw ν) {path |
        (ε : ℝ) ≤
          (Finset.range (length + 1)).sup' Finset.nonempty_range_add_one
            fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} ≤
      ENNReal.ofReal ((length + 1 : ℝ) * variance id ν)
    simpa only [Nat.cast_add, Nat.cast_one] using hmax
  calc
    _ ≤ (iidSequenceLaw ν) {increment | ∀ k ≤ length,
          AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
        (iidSequenceLaw ν) {increment |
          ∃ k ∈ Finset.range (length + 1),
            radius ≤ |AdditivePath.blockSum start (k + 1) increment|} :=
      measure_startMargin_le_blockCorridor_add_largeDeviation
        (iidSequenceLaw ν) hradius.le start length
    _ ≤ _ := add_le_add_right hlarge _

/-- For centered unit-second-moment increments and any spatial scale tending
to infinity, every positive relative margin and additive error admit one
diffusive block constant such that, eventually and uniformly over starting
indices and intervals, the probability of a margin-constrained starting point
is bounded by the probability of remaining in the interval throughout the
block plus the error. -/
theorem exists_diffusiveBlockConstant_eventually_startMargin_le_corridor_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {radiusFactor tolerance : ℝ}
    (hradiusFactor : 0 < radiusFactor) (htolerance : 0 < tolerance) :
    ∃ constant > 0, ∀ᶠ n in atTop,
      ∀ (start : ℕ) (lower upper : ℝ),
        (iidSequenceLaw ν) {increment |
            lower + radiusFactor * scale n ≤ AdditivePath.displacement start increment ∧
              AdditivePath.displacement start increment ≤
                upper - radiusFactor * scale n} ≤
          (iidSequenceLaw ν) {increment |
              ∀ k ≤ Asymptotics.diffusiveBlockLength constant scale n,
                AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
            ENNReal.ofReal tolerance := by
  obtain ⟨constant, hconstant, hoscillation⟩ :=
    exists_scaledBlockConstant_eventually_measure_blockMaximum_le
      ν hν hscale hradiusFactor htolerance
  have hoscillation' : ∀ᶠ n in atTop, ∀ start : ℕ,
      (iidSequenceLaw ν) {path |
        ∃ k ∈ Finset.range (Asymptotics.diffusiveBlockLength constant scale n + 1),
          radiusFactor * scale n ≤
            |AdditivePath.blockSum start (k + 1) path|} ≤
        ENNReal.ofReal tolerance := by
    simpa [Asymptotics.diffusiveBlockLength, Asymptotics.floorBlockLength] using
      hoscillation
  refine ⟨constant, hconstant, ?_⟩
  filter_upwards [hoscillation', hscale.eventually (eventually_gt_atTop 0)]
    with n hn hscalePos
  intro start lower upper
  calc
    _ ≤ (iidSequenceLaw ν) {increment |
            ∀ k ≤ Asymptotics.diffusiveBlockLength constant scale n,
              AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} +
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range
                (Asymptotics.diffusiveBlockLength constant scale n + 1),
              radiusFactor * scale n ≤
                |AdditivePath.blockSum start (k + 1) increment|} :=
      measure_startMargin_le_blockCorridor_add_largeDeviation
        (iidSequenceLaw ν)
        (mul_nonneg hradiusFactor.le hscalePos.le)
        start (Asymptotics.diffusiveBlockLength constant scale n)
    _ ≤ _ := add_le_add_right (hn start) _

end ProbabilityTheory.RandomWalk

end
