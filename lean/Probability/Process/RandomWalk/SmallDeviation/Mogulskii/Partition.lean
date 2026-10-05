/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Normalized
public import Probability.Process.RandomWalk.Path.Block.Partition
public import Probability.Process.RandomWalk.Kernel.Killed.Partition
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.FiniteDimensional
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Tightness.Maximal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Tightness

/-!
# Finite-partition endpoint bounds

Finite-dimensional Gaussian block estimates are transferred to simultaneous
corridor constraints at all endpoints of an equal-length partition.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- If a deterministic reference path has enough margin at every partition
endpoint, then a product of Gaussian block probabilities bounds the liminf
probability that all normalized random-walk endpoints stay in their assigned
open intervals. -/
theorem prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} {radius : ℝ} (hradius : 0 < radius)
    (target lower upper : ℕ → ℝ)
    (hmargin : ∀ k ≤ blocks,
      lower k + (blocks : ℝ) * radius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper k - (blocks : ℝ) * radius) :
    (∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target j - radius) / Real.sqrt constant)
            ((target j + radius) / Real.sqrt constant))) ≤
      atTop.liminf (fun n =>
        (independentIncrementLaw ν) {increment |
          ∀ k ≤ blocks,
            AdditivePath.displacement
                (k * diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower k) (upper k)}) := by
  let lowerBlock : Fin blocks → ℝ := fun j => target j - radius
  let upperBlock : Fin blocks → ℝ := fun j => target j + radius
  have hbox := prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums
    ν hcentered hsecondMoment hscale hconstant blocks lowerBlock upperBlock
  refine hbox.trans (Filter.liminf_le_liminf ?_)
  filter_upwards [] with n
  apply measure_mono
  intro increment hincrement
  apply normalized_partitionEndpoints_mem_Ioo_of_blockApproximation
    (target := target) hradius.le
  · intro j hj
    have hjBox := hincrement ⟨j, hj⟩
    simp only [lowerBlock, upperBlock, Set.mem_Ioo] at hjBox
    apply le_of_lt
    rw [abs_lt]
    constructor <;> linarith
  · exact hmargin

/-- Under the centered unit-second-moment assumptions, simultaneous margins at
the starts of finitely many blocks are bounded by the probability of staying
inside every block corridor, plus the sum of the explicit maximal-inequality
errors. -/
theorem measure_partitionStartMargins_le_corridors_add_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {blocks length : ℕ} {radius : ℝ} (hradius : 0 < radius)
    (lower upper : ℕ → ℝ) :
    (independentIncrementLaw ν) {increment | ∀ j < blocks,
        lower j + radius ≤ AdditivePath.displacement (j * length) increment ∧
          AdditivePath.displacement (j * length) increment ≤ upper j - radius} ≤
      (independentIncrementLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          AdditivePath.displacement (j * length + k) increment ∈
            Set.Icc (lower j) (upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal ((length + 1 : ℝ) / radius ^ 2) := by
  refine (measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
    (independentIncrementLaw ν) hradius.le lower upper).trans ?_
  apply add_le_add_right
  exact Finset.sum_le_sum fun j hj =>
    measure_exists_abs_blockSum_ge_le ν hν (j * length) hradius length

/-- A normalized finite-partition endpoint event controls the full
unnormalized path on every block, with the explicit sum of within-block
oscillation errors. -/
theorem measure_normalizedEndpoints_le_corridors_add_error
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {blocks length : ℕ} {scale radius : ℝ}
    (hscale : 0 < scale) (hradius : 0 < radius)
    (lower upper : ℕ → ℝ) :
    (independentIncrementLaw ν) {increment | ∀ j < blocks,
        AdditivePath.displacement (j * length) increment / scale ∈
          Set.Ioo (lower j + radius) (upper j - radius)} ≤
      (independentIncrementLaw ν) {increment | ∀ j < blocks, ∀ k ≤ length,
          AdditivePath.displacement (j * length + k) increment ∈
            Set.Icc (scale * lower j) (scale * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal ((length + 1 : ℝ) / (scale * radius) ^ 2) := by
  calc
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          scale * lower j + scale * radius ≤
              AdditivePath.displacement (j * length) increment ∧
            AdditivePath.displacement (j * length) increment ≤
              scale * upper j - scale * radius} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (independentIncrementLaw ν) hscale lower upper
    _ ≤ _ := measure_partitionStartMargins_le_corridors_add_error
      ν hν (mul_pos hscale hradius) (fun j => scale * lower j)
        (fun j => scale * upper j)

/-- For a fixed positive number of blocks, the block length can be chosen so
that normalized endpoint containment controls all within-block positions with
an arbitrarily small total error.  The estimate is uniform in the corridor
endpoints. -/
theorem exists_diffusiveBlockConstant_eventually_normalizedEndpoints_le_corridors_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {radiusFactor tolerance : ℝ}
    (hradiusFactor : 0 < radiusFactor) (htolerance : 0 < tolerance) :
    ∃ constant > 0, ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      (independentIncrementLaw ν) {increment | ∀ j < blocks,
          AdditivePath.displacement
              (j * diffusiveBlockLength constant scale n) increment /
              scale n ∈
            Set.Ioo (lower j + radiusFactor) (upper j - radiusFactor)} ≤
        (independentIncrementLaw ν) {increment | ∀ j < blocks,
            ∀ k ≤ diffusiveBlockLength constant scale n,
              AdditivePath.displacement
                  (j * diffusiveBlockLength constant scale n + k) increment ∈
                Set.Icc (scale n * lower j) (scale n * upper j)} +
          ENNReal.ofReal tolerance := by
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hperBlock : 0 < tolerance / (blocks : ℝ) :=
    div_pos htolerance hblocksReal
  obtain ⟨constant, hconstant, hoscillation⟩ :=
    exists_diffusiveBlockConstant_eventually_measure_max_le
      ν hν hscale hradiusFactor hperBlock
  refine ⟨constant, hconstant, ?_⟩
  filter_upwards [hoscillation, _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale]
    with n hn hscalePos
  intro lower upper
  let length := diffusiveBlockLength constant scale n
  calc
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          scale n * lower j + scale n * radiusFactor ≤
              AdditivePath.displacement (j * length) increment ∧
            AdditivePath.displacement (j * length) increment ≤
              scale n * upper j - scale n * radiusFactor} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (independentIncrementLaw ν) hscalePos lower upper
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ j ∈ Finset.range blocks,
          (independentIncrementLaw ν) {increment |
            ∃ k ∈ Finset.range (length + 1),
              scale n * radiusFactor ≤
                |AdditivePath.blockSum (j * length) (k + 1) increment|} :=
      measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
        (independentIncrementLaw ν)
        (mul_nonneg hscalePos.le hradiusFactor.le)
        (fun j => scale n * lower j) (fun j => scale n * upper j)
    _ ≤ (independentIncrementLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (tolerance / (blocks : ℝ)) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [independentIncrementLaw, length, mul_comm] using
        hn (j * length)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]
      congr 1
      field_simp [hblocksReal.ne']

/-- Finite-dimensional Gaussian convergence and within-block tightness combine
into a lower bound for simultaneous full-block corridors.  All blocks use the
same diffusive length, and the total approximation loss is the prescribed
`tolerance`. -/
theorem exists_diffusiveBlockConstant_gaussianProduct_le_liminf_corridors_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {endpointMargin blockRadius tolerance : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (htolerance : 0 < tolerance)
    (target lower upper : ℕ → ℝ)
    (hmargin : ∀ k ≤ blocks,
      lower k + endpointMargin + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper k - endpointMargin - (blocks : ℝ) * blockRadius) :
    ∃ constant > 0,
      (∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target j - blockRadius) / Real.sqrt constant)
              ((target j + blockRadius) / Real.sqrt constant))) ≤
        atTop.liminf (fun n =>
          (independentIncrementLaw ν) {increment | ∀ j < blocks,
              ∀ k ≤ diffusiveBlockLength constant scale n,
                AdditivePath.displacement
                    (j * diffusiveBlockLength constant scale n + k) increment ∈
                  Set.Icc (scale n * lower j) (scale n * upper j)} +
            ENNReal.ofReal tolerance) := by
  obtain ⟨constant, hconstant, hcontrol⟩ :=
    exists_diffusiveBlockConstant_eventually_normalizedEndpoints_le_corridors_add
      ν hν hscale hblocks hendpointMargin htolerance
  refine ⟨constant, hconstant, ?_⟩
  have hendpoint :=
    prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints
      ν hν.1 hν.2 hscale hconstant hblockRadius target
      (fun k => lower k + endpointMargin)
      (fun k => upper k - endpointMargin) (by
        intro k hk
        have hm := hmargin k hk
        constructor <;> linarith)
  refine hendpoint.trans (Filter.liminf_le_liminf ?_)
  filter_upwards [hcontrol] with n hn
  refine (measure_mono ?_).trans (hn lower upper)
  intro increment hincrement j hj
  exact hincrement j hj.le

/-- For every fixed normalized starting point in a horizontal interval, the
finite-partition Gaussian lower bound transfers to the remaining mass of the
corresponding killed additive kernel.  This is the one-block input expected by
the abstract sub-Markov blocking lemmas. -/
theorem exists_diffusiveBlockConstant_gaussianProduct_le_liminf_remainingMass_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper initial endpointMargin blockRadius tolerance : ℝ}
    (hinitial : initial ∈ Set.Icc lower upper)
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (htolerance : 0 < tolerance)
    (target : ℕ → ℝ)
    (hmargin : ∀ k ≤ blocks,
      lower - initial + endpointMargin + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper - initial - endpointMargin -
            (blocks : ℝ) * blockRadius) :
    ∃ constant > 0,
      (∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target j - blockRadius) / Real.sqrt constant)
              ((target j + blockRadius) / Real.sqrt constant))) ≤
        atTop.liminf (fun n =>
          Kernel.remainingMass
              (killedIncrementKernel ν
                (Set.Icc (scale n * lower) (scale n * upper))
                measurableSet_Icc)
              (blocks * diffusiveBlockLength constant scale n)
              (scale n * initial) +
            ENNReal.ofReal tolerance) := by
  obtain ⟨constant, hconstant, hbound⟩ :=
    exists_diffusiveBlockConstant_gaussianProduct_le_liminf_corridors_add
      ν hν hscale hblocks hendpointMargin hblockRadius htolerance target
      (fun _ => lower - initial) (fun _ => upper - initial) (by
        intro k hk
        simpa using hmargin k hk)
  refine ⟨constant, hconstant, hbound.trans (Filter.liminf_le_liminf ?_)⟩
  filter_upwards [_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale,
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_diffusiveBlockLength_pos hscale hconstant]
    with n hscalePos hlength
  have hinitialScaled : scale n * initial ∈
      Set.Icc (scale n * lower) (scale n * upper) := by
    constructor <;> nlinarith [hinitial.1, hinitial.2]
  have hkernel :=
    killedIncrementKernel_Icc_remainingMass_mul_eq_blockCorridors
      ν (scale n * lower) (scale n * upper) (scale n * initial)
      hinitialScaled hblocks hlength
  have hevent :
      {increment : ℕ → ℝ | ∀ j < blocks,
          ∀ k ≤ diffusiveBlockLength constant scale n,
            AdditivePath.displacement
                (j * diffusiveBlockLength constant scale n + k) increment ∈
              Set.Icc (scale n * (lower - initial))
                (scale n * (upper - initial))} =
        {increment | ∀ j < blocks,
          ∀ k ≤ diffusiveBlockLength constant scale n,
            scale n * initial +
                AdditivePath.displacement
                  (j * diffusiveBlockLength constant scale n + k) increment ∈
              Set.Icc (scale n * lower) (scale n * upper)} := by
    ext increment
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor <;> intro h j hj k hk
    · have hp := h j hj k hk
      constructor <;> nlinarith
    · have hp := h j hj k hk
      constructor <;> nlinarith
  rw [hevent, ← hkernel]

end ProbabilityTheory.RandomWalk
