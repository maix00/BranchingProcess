/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Distributions.Gaussian.Interval
import Probability.Distributions.Moments.Real
import Probability.Process.RandomWalk.Path.Block.Partition.Normalized
import Analysis.Asymptotics.Scale.Block.Diffusive
import Probability.Sequence.IID.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.Lemmas.OpenBox

/-!
# Gaussian finite-partition lower bounds

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums`:
  for centered unit-variance increments, $s_n\to\infty$, $c>0$, and finite
  open intervals $(a_j,b_j)$,
  \[
    \prod_{j<m}\mathbb P\!\left(Z\in
      \left(\frac{a_j}{\sqrt c},\frac{b_j}{\sqrt c}\right)\right)
    \leq \liminf_{n\to\infty}\mathbb P_\nu\!\left(
      \frac{S_{(j+1)q_n}-S_{jq_n}}{s_n}\in(a_j,b_j)\ \text{for all }j<m
    \right),\qquad q_n=\operatorname{diffusiveBlockLength}(c,s,n),
  \]
  where $Z\sim N(0,1)$ and $S_k$ is the IID partial sum.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints`:
  with the same centered unit-variance and scale assumptions, $c>0$, and
  $r>0$, if for every $k\leq m$
  \[
    \ell_k+mr<\sum_{j<k}x_j<u_k-mr,
  \]
  then
  \[
    \prod_{j<m}\mathbb P\!\left(Z\in
      \left(\frac{x_j-r}{\sqrt c},\frac{x_j+r}{\sqrt c}\right)\right)
    \leq \liminf_{n\to\infty}\mathbb P_\nu\!\left(
      \frac{S_{kq_n}}{s_n}\in(\ell_k,u_k)\ \text{for all }k\leq m
    \right).
  \]

This proof module combines two consecutive estimates used by the finite-reference
survival argument. First, for centered unit-variance increments, the product of
Gaussian interval probabilities bounds the liminf probability that each of
finitely many normalized diffusive block sums lies in its assigned open
interval. Second, a deterministic margin condition transfers that estimate to
all endpoints of a finite partition. Both declarations are proof-chain lemmas;
the reusable consecutive-block limit and open-set Portmanteau theorem remain at
their general owners.

These estimates support the Gaussian proof of Theorem 3, Section 4, p. 764 of
A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
-/

section

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

/-- For centered unit-variance increments and a spatial scale tending to
infinity, the product
of the Gaussian interval probabilities is a lower bound for the liminf
probability that every normalized diffusive block sum lies in its assigned
open interval. This is the finite-dimensional block input to Theorem 3,
Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081. -/
lemma prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ)
    (lower upper : Fin blocks → ℝ) :
    (∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo (lower j / Real.sqrt constant)
            (upper j / Real.sqrt constant))) ≤
      atTop.liminf (fun n =>
        (iidSequenceLaw ν) {increment |
          ∀ j : Fin blocks,
            AdditivePath.blockSum
                (j * Asymptotics.diffusiveBlockLength constant scale n)
                (Asymptotics.diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower j) (upper j)}) := by
  rw [← measure_gaussianBlockBox_eq_prod hconstant lower upper]
  exact measure_gaussianBlockBox_le_liminf ν hcentered hsecondMoment
    hscale hconstant blocks lower upper

/-- If a deterministic reference path has enough margin at every partition
endpoint, then a product of Gaussian block probabilities bounds the liminf
probability that all normalized random-walk endpoints stay in their assigned
open intervals, provided the spatial scale tends to infinity. This
finite-partition estimate is used in the Gaussian block
argument for Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081. -/
lemma prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
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
                (k * Asymptotics.diffusiveBlockLength constant scale n) increment /
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
