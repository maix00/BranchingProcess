/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Core
public import Probability.Process.RandomWalk.Path.Block.Partition.Normalized
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Path.Tightness
import Probability.Process.RandomWalk.Path.Block.Partition.Maximal

/-!
# Finite-partition corridor tightness

Write $D_k=\operatorname{AdditivePath.displacement}(k,\cdot)$,
$q_n=\operatorname{diffusiveBlockLength}(C,s,n)$ and, for an increment law
$\nu$, let $\mathbb P_\nu=\operatorname{iidSequenceLaw}(\nu)$. The public
declarations in `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii` are:

For $C,\rho,e>0$, the fixed-constant estimate is
\[
\mathbb P_\nu\!\left(\forall j<m,\,
  \frac{D_{j q_n}}{s_n}\in(a_j+\rho,b_j-\rho)\right)
\leq
\mathbb P_\nu\!\left(\forall j<m,\ \forall k\leq q_n,\,
  D_{j q_n+k}\in[s_n a_j,s_n b_j]\right)
 +\operatorname{ofReal}\!\left(m\left(\frac{C}{\rho^2}+e\right)\right),
\]
eventually in $n$, uniformly over $(a_j),(b_j)$. The first declaration
chooses $C$ so the total error is below any prescribed positive tolerance;
the third retains this comparison after intersecting both path events with
one fixed event.

- `exists_diffusiveBlockConstant_eventually_normalizedEndpoints_le_corridors_add`:
  for a fixed finite number of blocks, a positive endpoint margin and error,
  and a Mogulskii scale, some $C>0$ makes normalized endpoint containment
  control every full block corridor eventually, uniformly in the corridor
  bounds.
- `eventually_normalizedEndpoints_le_corridors_add_explicitError`: for a
  fixed $C,\rho,e>0$, the same probability comparison eventually has total
  error at most $\operatorname{ofReal}(m(C/\rho^2+e))$.
- `eventually_normalizedEndpoints_inter_le_corridors_inter_add_explicitError`:
  the fixed-$C$ comparison remains valid after intersecting both events with
  any fixed event of the full increment sequence.

The estimates combine the diffusive-block maximal bound with the generic
finite-partition path comparison. They supply the endpoint-to-corridor step
used by Gaussian block survival and return-kernel lower bounds in Theorem 3,
Section 4 of A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii



/-- With a fixed positive diffusive block constant, normalized endpoint
containment controls all block corridors up to the explicit asymptotic
maximal-inequality error. -/
theorem eventually_normalizedEndpoints_le_corridors_add_explicitError
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant radiusFactor error : ℝ}
    (hconstant : 0 < constant) (hradiusFactor : 0 < radiusFactor)
    (herror : 0 < error) (blocks : ℕ) :
    ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      (iidSequenceLaw ν) {increment | ∀ j < blocks,
          AdditivePath.displacement
              (j * diffusiveBlockLength constant scale n) increment /
              scale n ∈
            Set.Ioo (lower j + radiusFactor) (upper j - radiusFactor)} ≤
        (iidSequenceLaw ν) {increment | ∀ j < blocks,
            ∀ k ≤ diffusiveBlockLength constant scale n,
              AdditivePath.displacement
                  (j * diffusiveBlockLength constant scale n + k) increment ∈
                Set.Icc (scale n * lower j) (scale n * upper j)} +
          ENNReal.ofReal
            (blocks * (constant / radiusFactor ^ 2 + error)) := by
  have hoscillation := eventually_measure_diffusiveBlockMaximum_le
    ν hν hscale hconstant hradiusFactor herror
  filter_upwards [hoscillation, _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale]
    with n hn hscalePos
  intro lower upper
  let length := diffusiveBlockLength constant scale n
  calc
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          scale n * lower j + scale n * radiusFactor ≤
              AdditivePath.displacement (j * length) increment ∧
            AdditivePath.displacement (j * length) increment ≤
              scale n * upper j - scale n * radiusFactor} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (iidSequenceLaw ν) hscalePos lower upper
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ j ∈ Finset.range blocks,
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range (length + 1),
              scale n * radiusFactor ≤
                |AdditivePath.blockSum (j * length) (k + 1) increment|} :=
      measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
        (iidSequenceLaw ν)
        (mul_nonneg hscalePos.le hradiusFactor.le)
        (fun j => scale n * lower j) (fun j => scale n * upper j)
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (constant / radiusFactor ^ 2 + error) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [iidSequenceLaw, length, mul_comm] using
        hn (j * length)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]

/-- The fixed-constant estimate also preserves an arbitrary final endpoint
event.  This is the form used by an outer-corridor/inner-return block kernel. -/
theorem eventually_normalizedEndpoints_inter_le_corridors_inter_add_explicitError
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant radiusFactor error : ℝ}
    (hconstant : 0 < constant) (hradiusFactor : 0 < radiusFactor)
    (herror : 0 < error) (blocks : ℕ) :
    ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      ∀ final : Set (ℕ → ℝ),
      (iidSequenceLaw ν)
          ({increment | ∀ j < blocks,
            AdditivePath.displacement
                (j * diffusiveBlockLength constant scale n) increment /
                scale n ∈
              Set.Ioo (lower j + radiusFactor)
                (upper j - radiusFactor)} ∩ final) ≤
        (iidSequenceLaw ν)
            ({increment | ∀ j < blocks,
              ∀ k ≤ diffusiveBlockLength constant scale n,
                AdditivePath.displacement
                    (j * diffusiveBlockLength constant scale n + k)
                      increment ∈
                  Set.Icc (scale n * lower j)
                    (scale n * upper j)} ∩ final) +
          ENNReal.ofReal
            (blocks * (constant / radiusFactor ^ 2 + error)) := by
  have hoscillation := eventually_measure_diffusiveBlockMaximum_le
    ν hν hscale hconstant hradiusFactor herror
  filter_upwards [hoscillation, _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale]
    with n hn hscalePos
  intro lower upper final
  let length := diffusiveBlockLength constant scale n
  calc
    _ ≤ (iidSequenceLaw ν)
          ({increment | ∀ j < blocks, ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} ∩ final) +
        ∑ j ∈ Finset.range blocks,
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range (length + 1),
              scale n * radiusFactor ≤
                |AdditivePath.blockSum (j * length) (k + 1) increment|} :=
      measure_normalizedEndpoints_inter_le_corridors_inter_add_sum_largeDeviation
        (iidSequenceLaw ν) hscalePos hradiusFactor.le lower upper final
    _ ≤ (iidSequenceLaw ν)
          ({increment | ∀ j < blocks, ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} ∩ final) +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (constant / radiusFactor ^ 2 + error) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [iidSequenceLaw, length, mul_comm] using
        hn (j * length)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]

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
      (iidSequenceLaw ν) {increment | ∀ j < blocks,
          AdditivePath.displacement
              (j * diffusiveBlockLength constant scale n) increment /
              scale n ∈
            Set.Ioo (lower j + radiusFactor) (upper j - radiusFactor)} ≤
        (iidSequenceLaw ν) {increment | ∀ j < blocks,
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
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          scale n * lower j + scale n * radiusFactor ≤
              AdditivePath.displacement (j * length) increment ∧
            AdditivePath.displacement (j * length) increment ≤
              scale n * upper j - scale n * radiusFactor} :=
      measure_normalizedEndpoints_le_partitionStartMargins
        (iidSequenceLaw ν) hscalePos lower upper
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ j ∈ Finset.range blocks,
          (iidSequenceLaw ν) {increment |
            ∃ k ∈ Finset.range (length + 1),
              scale n * radiusFactor ≤
                |AdditivePath.blockSum (j * length) (k + 1) increment|} :=
      measure_partitionStartMargins_le_corridors_add_sum_largeDeviation
        (iidSequenceLaw ν)
        (mul_nonneg hscalePos.le hradiusFactor.le)
        (fun j => scale n * lower j) (fun j => scale n * upper j)
    _ ≤ (iidSequenceLaw ν) {increment | ∀ j < blocks,
          ∀ k ≤ length,
            AdditivePath.displacement (j * length + k) increment ∈
              Set.Icc (scale n * lower j) (scale n * upper j)} +
        ∑ _j ∈ Finset.range blocks,
          ENNReal.ofReal (tolerance / (blocks : ℝ)) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [iidSequenceLaw, length, mul_comm] using
        hn (j * length)
    _ = _ := by
      congr 1
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg blocks)]
      congr 1
      field_simp [hblocksReal.ne']

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
