/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Gaussian.Interval
public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.Path.Block.Partition.Normalized
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.Lemmas.BlockVector
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.BlockScale

/-!
# Gaussian lower bounds for finite-partition endpoints

For a centered unit-variance increment law $\nu$, a Mogulskii scale $s$, and
$q_n=\operatorname{diffusiveBlockLength}(C,s,n)$, the public declaration
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints`
states the following. Given $C,\rho>0$ and endpoint intervals $(a_k,b_k)$,
if a deterministic target path has margin $m\rho$ from each endpoint, then
\[
\prod_{j<m}\mathbb P\!\left(Z\in
  \left(\frac{y_j-\rho}{\sqrt C},\frac{y_j+\rho}{\sqrt C}\right)\right)
\le \liminf_{n\to\infty}\mathbb P_\nu\!\left(
  \frac{D_{kq_n}}{s_n}\in(a_k,b_k)\text{ for every }k\le m\right),
\]
where $Z\sim N(0,1)$ and $D_k=\operatorname{AdditivePath.displacement}(k,\cdot)$.

This finite-dimensional endpoint estimate is the Gaussian block input to the
finite-reference survival bounds in Theorem 3, Section 4 of A. A. Mogul'skii,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

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
        (iidSequenceLaw ν) {increment |
          ∀ k ≤ blocks,
            AdditivePath.displacement
                (k * diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower k) (upper k)}) := by
  let lowerBlock : Fin blocks → ℝ := fun j => target j - radius
  let upperBlock : Fin blocks → ℝ := fun j => target j + radius
  have hbox :=
    prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

end
