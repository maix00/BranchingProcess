/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Maximal.Basic
public import Probability.Distributions.Moments.Real
public import Analysis.Asymptotics.Scale.Block.Length

/-!
# Maximal bounds under centered second-moment assumptions

The abstract block maximal inequality is specialized here to centered
unit-second-moment increments.  This is the quantitative input used to control
within-block oscillations in path tightness arguments.

## Public declarations

- `ProbabilityTheory.RandomWalk.maximal_ineq_sq_blockSum_of_centeredUnitSecondMoment`:
  the squared maximal inequality holds on every deterministic increment block.
- `ProbabilityTheory.RandomWalk.measure_sq_le_blockMaximum_le`:
  $\mathbb P(\max_{j\le n}|S_j|\ge r)\le(n+1)/r^2$ for $r>0$.
- `ProbabilityTheory.RandomWalk.measure_exists_abs_blockSum_ge_le`:
  the same estimate for the event that some block partial sum has absolute
  value at least $r$.
- `ProbabilityTheory.RandomWalk.eventually_measure_blockMaximum_le_of_tendsto_ratio`:
  if $r_n>0$ eventually and $(\ell_n+1)/r_n^2\to c$, then for $e>0$,
  uniformly over deterministic block starts, the probability of a block
  displacement at least $r_n$ is eventually at most
  $\operatorname{ofReal}(c+e)$.
- `ProbabilityTheory.RandomWalk.exists_scaledBlockConstant_eventually_measure_blockMaximum_le`:
  if $s_n\to\infty$, then for every $\rho,\epsilon>0$ some $c>0$ makes the
  same probability at most $\operatorname{ofReal}(\epsilon)$ for block length
  $\lfloor c s_n^2\rfloor$, eventually and uniformly over block starts.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Under the centered unit-second-moment assumptions, every deterministic
increment block satisfies the same squared maximal estimate. -/
theorem maximal_ineq_sq_blockSum_of_centeredUnitSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    (start : ℕ) (ε : ℝ≥0) (n : ℕ) :
    ε * (iidSequenceLaw ν) {path | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} ≤
      ENNReal.ofReal (n + 1 : ℝ) := by
  have hvariance : variance id ν = 1 := by
    rw [variance_of_integral_eq_zero measurable_id.aemeasurable
      (by simpa [id] using hν.1)]
    simpa [id] using hν.2
  simpa [hvariance] using
    maximal_ineq_sq_blockSum_iidSequenceLaw ν hν.memLp_two hν.1
      start ε n

/-- Probability form of the block maximal estimate: during `n + 1` exposed
increments, exceeding a positive radius has probability at most
`(n + 1) / radius²`. -/
theorem measure_sq_le_blockMaximum_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    (start : ℕ) {radius : ℝ} (hradius : 0 < radius) (n : ℕ) :
    (iidSequenceLaw ν) {path | radius ^ 2 ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} ≤
      ENNReal.ofReal ((n + 1 : ℝ) / radius ^ 2) := by
  let ε : ℝ≥0 := ⟨radius ^ 2, sq_nonneg radius⟩
  have hmax := maximal_ineq_sq_blockSum_of_centeredUnitSecondMoment
    ν hν start ε n
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos hradius)]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hradius)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  rw [mul_comm]
  have hε : (ε : ENNReal) = ENNReal.ofReal (radius ^ 2) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  rw [← hε]
  change (ε : ENNReal) * (iidSequenceLaw ν) {path | (ε : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} ≤
    ENNReal.ofReal (n + 1 : ℝ)
  exact hmax

/-- Equivalent absolute-value formulation of the block maximal estimate. -/
theorem measure_exists_abs_blockSum_ge_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    (start : ℕ) {radius : ℝ} (hradius : 0 < radius) (n : ℕ) :
    (iidSequenceLaw ν) {path |
        ∃ k ∈ Finset.range (n + 1),
          radius ≤ |AdditivePath.blockSum start (k + 1) path|} ≤
      ENNReal.ofReal ((n + 1 : ℝ) / radius ^ 2) := by
  have hevent :
      {path : ℕ → ℝ | radius ^ 2 ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
            fun k => (AdditivePath.blockSum start (k + 1) path) ^ 2} =
        {path | ∃ k ∈ Finset.range (n + 1),
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
  rw [← hevent]
  exact measure_sq_le_blockMaximum_le ν hν start hradius n

/-- If the squared block scale has a limiting length ratio, then the
probability that a block partial sum exceeds a fixed fraction of that scale
has the corresponding eventual maximal bound. -/
theorem eventually_measure_blockMaximum_le_of_tendsto_ratio
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {threshold : ℕ → ℝ} {length : ℕ → ℕ}
    (hthresholdPos : ∀ᶠ n in atTop, 0 < threshold n)
    {limit error : ℝ} (herror : 0 < error)
    (hratio : Tendsto (fun n =>
        ((length n + 1 : ℕ) : ℝ) / threshold n ^ 2)
      atTop (nhds limit)) :
    ∀ᶠ n in atTop, ∀ start : ℕ,
      (iidSequenceLaw ν) {path |
        ∃ k ∈ Finset.range (length n + 1),
          threshold n ≤
            |AdditivePath.blockSum start (k + 1) path|} ≤
        ENNReal.ofReal (limit + error) := by
  have hratioUpper : ∀ᶠ n in atTop,
      ((length n + 1 : ℕ) : ℝ) / threshold n ^ 2 < limit + error :=
    hratio.eventually (Iio_mem_nhds (lt_add_of_pos_right _ herror))
  filter_upwards [hthresholdPos, hratioUpper] with n hthresholdPos hn start
  calc
    (iidSequenceLaw ν) {path |
        ∃ k ∈ Finset.range (length n + 1),
          threshold n ≤
            |AdditivePath.blockSum start (k + 1) path|} ≤
      ENNReal.ofReal
        (((length n + 1 : ℕ) : ℝ) / threshold n ^ 2) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        measure_exists_abs_blockSum_ge_le ν hν start
          hthresholdPos (length n)
    _ ≤ ENNReal.ofReal (limit + error) :=
      ENNReal.ofReal_le_ofReal hn.le

/-- For every positive tolerance, a diverging spatial scale admits a
quadratic block length whose maximal-displacement probability is eventually
below that tolerance, uniformly over the deterministic block start. -/
theorem exists_scaledBlockConstant_eventually_measure_blockMaximum_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {radiusFactor tolerance : ℝ}
    (hradiusFactor : 0 < radiusFactor) (htolerance : 0 < tolerance) :
    ∃ constant > 0, ∀ᶠ n in atTop, ∀ start : ℕ,
      (iidSequenceLaw ν) {path |
        ∃ k ∈ Finset.range
            (Asymptotics.floorBlockLength
              (fun n => constant * scale n ^ 2) n + 1),
          radiusFactor * scale n ≤
            |AdditivePath.blockSum start (k + 1) path|} ≤
        ENNReal.ofReal tolerance := by
  let constant : ℝ := tolerance * radiusFactor ^ 2 / 2
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  let length : ℕ → ℕ := fun n =>
    Asymptotics.floorBlockLength (fun n => constant * scale n ^ 2) n
  have hfloorRatio :=
    Asymptotics.tendsto_floorBlockLength_div_sq_of_tendsto_atTop
      hscale hconstant
  have hinv : Tendsto (fun n => (scale n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hscale
  have hinvSq : Tendsto (fun n => (scale n)⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hinv.pow 2
  have honeDiv : Tendsto (fun n => 1 / scale n ^ 2) atTop (nhds 0) := by
    convert hinvSq using 1
    funext n
    field_simp
  have hlengthRatio : Tendsto (fun n =>
      ((length n + 1 : ℕ) : ℝ) / scale n ^ 2)
      atTop (nhds constant) := by
    have hsum := hfloorRatio.add honeDiv
    have heq : (fun n =>
        ((length n + 1 : ℕ) : ℝ) / scale n ^ 2) =ᶠ[atTop]
        fun n => (length n : ℝ) / scale n ^ 2 + 1 / scale n ^ 2 := by
      filter_upwards [hscalePos] with n hn
      dsimp [length]
      push_cast
      field_simp [hn.ne']
    have hsum' := hsum.congr' heq.symm
    simpa using hsum'
  let threshold : ℕ → ℝ := fun n => radiusFactor * scale n
  have hthresholdPos : ∀ᶠ n in atTop, 0 < threshold n := by
    filter_upwards [hscalePos] with n hn
    exact mul_pos hradiusFactor hn
  have hratio : Tendsto (fun n =>
      ((length n + 1 : ℕ) : ℝ) / threshold n ^ 2)
      atTop (nhds (constant / radiusFactor ^ 2)) := by
    have hdiv := hlengthRatio.div_const (radiusFactor ^ 2)
    convert hdiv.congr' ?_ using 1
    filter_upwards [hscalePos] with n hn
    dsimp [threshold]
    field_simp [hradiusFactor.ne', hn.ne']
  have hoscillation := eventually_measure_blockMaximum_le_of_tendsto_ratio
    ν hν hthresholdPos (half_pos htolerance) hratio
  have hbound : constant / radiusFactor ^ 2 + tolerance / 2 = tolerance := by
    dsimp [constant]
    field_simp [hradiusFactor.ne']
    ring
  refine ⟨constant, hconstant, ?_⟩
  simpa [length, threshold, hbound] using hoscillation

end ProbabilityTheory.RandomWalk
