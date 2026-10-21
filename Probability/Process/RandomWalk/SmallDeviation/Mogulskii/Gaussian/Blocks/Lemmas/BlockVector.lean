/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.BlockScale
import Probability.ConvergenceInDistribution.Basic
public import Probability.Distributions.Stable.Gaussian.Basic

import Probability.Process.RandomWalk.FunctionalLimit.FiniteDimensional.IndependentBlocks
import Probability.Distributions.Stable.Attraction.Normal.Basic
import Probability.ConvergenceInDistribution.Portmanteau

/-!
# Proof lemmas for Gaussian block-vector estimates

Let $b_n=\lfloor c x_n^2\rfloor$ and
$B_{n,j}=\frac{S_{(j+1)b_n}-S_{jb_n}}{x_n}$ for $j<m$.
This module combines the generic consecutive-block limit with the Gaussian
open-set bound and product factorization. Its final endpoint-box estimate is
consumed by `PartitionEndpoints.lean`; the preceding vector and box claims
are private proof steps, not separate interfaces.

The cross-module lemma is
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums`:
for centered unit-variance increments, $q_n=\lfloor c s_n^2\rfloor$, and
interval endpoints $a_j,b_j$, it gives
\[
  \prod_{j<m}\mathbb P\!\left(\frac{a_j}{\sqrt c}<Z<\frac{b_j}{\sqrt c}\right)
  \leq \liminf_{n\to\infty}
  \mathbb P\!\left(\frac{S_{(j+1)q_n}-S_{jq_n}}{s_n}\in(a_j,b_j)\;
    \text{for every }j<m\right),
\]
where $Z\sim N(0,1)$.

These are finite-dimensional inputs for the block argument in Theorem 3,
Section 4, p. 764 of the 1974 Russian original by A. A. Mogul'skii, “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081. The endpoint CLT comes from the Donsker
layer; this file does not assert tightness in path space.
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

/-- Any fixed finite vector of consecutive diffusive block sums converges to
independent centered Gaussian increments. This is the finite-dimensional
block limit used in Theorem 3, Section 4, p. 764 of A. A. Mogul'skii,
*Small Deviations in a Space of Trajectories* (DOI 10.1137/1119081). -/
private theorem tendstoInDistribution_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin blocks) =>
        let length := diffusiveBlockLength constant scale n
        AdditivePath.blockSum (j * length) length increment / scale n)
      atTop
      (fun z (j : Fin blocks) => z j * Real.sqrt constant)
      (fun _ => iidSequenceLaw ν)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 1) := by
  let normalization : ℕ → ℝ := fun n => Real.sqrt n
  let length : ℕ → ℕ → ℕ :=
    fun n _ => diffusiveBlockLength constant scale n
  let ratio : Fin blocks → ℝ := fun _ => Real.sqrt constant
  let shift : Fin blocks → ℝ := fun _ => 0
  have hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0) := by
    simpa [normalization] using
      ProbabilityTheory.isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_unitSecondMoment
        ν ⟨hcentered, hsecondMoment⟩
  have hlength (j : Fin blocks) :
      Tendsto (fun n => length n j.val) atTop atTop := by
    simpa [length] using
      IsMogulskiiScale.tendsto_diffusiveBlockLength_atTop hscale hconstant
  have hscalePos : ∀ᶠ n : ℕ in atTop, scale n ≠ 0 := by
    filter_upwards [IsMogulskiiScale.eventually_pos hscale] with n hn
    exact hn.ne'
  have hratio (j : Fin blocks) :
      Tendsto (fun n => normalization (length n j.val) / scale n)
        atTop (nhds (ratio j)) := by
    simpa [normalization, length, ratio] using
      IsMogulskiiScale.tendsto_sqrt_diffusiveBlockLength_div hscale hconstant
  have hcenter (j : Fin blocks) :
      Tendsto (fun n => (0 : ℝ) / scale n) atTop (nhds (shift j)) := by
    simp [shift]
  have hblocks :=
    ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockSums
      hDOA blocks length scale ratio shift hlength hscalePos hratio hcenter
  have hstart (n : ℕ) (j : Fin blocks) :
      AdditivePath.blockStart (length n) j.val =
        j.val * diffusiveBlockLength constant scale n := by
    simp [length, AdditivePath.blockStart_const]
  simpa [length, ratio, shift, hstart, mul_comm] using hblocks

/-- The limiting product-Gaussian probability of a finite open box is a
lower bound for the liminf of the corresponding normalized block-vector
probabilities. This is the open-set lower bound applied to the finite block
limit in Theorem 3, Section 4 of A. A. Mogul'skii, *Small Deviations in a
Space of Trajectories* (DOI 10.1137/1119081). -/
private theorem measure_gaussianBlockBox_le_liminf
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ)
    (lower upper : Fin blocks → ℝ) :
    (Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z j => z j * Real.sqrt constant)
        (Set.univ.pi fun j => Set.Ioo (lower j) (upper j)) ≤
      atTop.liminf (fun n =>
        (iidSequenceLaw ν) {increment |
          ∀ j : Fin blocks,
            AdditivePath.blockSum
                (j * diffusiveBlockLength constant scale n)
                (diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower j) (upper j)}) := by
  let X : ℕ → (ℕ → ℝ) → (Fin blocks → ℝ) := fun n increment j =>
    AdditivePath.blockSum
        (j * diffusiveBlockLength constant scale n)
        (diffusiveBlockLength constant scale n) increment / scale n
  let Z : (Fin blocks → ℝ) → (Fin blocks → ℝ) := fun z j =>
    z j * Real.sqrt constant
  let G : Set (Fin blocks → ℝ) :=
    Set.univ.pi fun j => Set.Ioo (lower j) (upper j)
  have hG : IsOpen G := isOpen_set_pi Set.finite_univ fun j _ => isOpen_Ioo
  have hconv := tendstoInDistribution_diffusiveBlockSums ν hcentered
    hsecondMoment hscale hconstant blocks
  have hbound := hconv.measure_map_le_liminf_of_isOpen hG
  have hX (n : ℕ) : Measurable (X n) := by
    rw [measurable_pi_iff]
    intro j
    exact (blockSum_measurable
      (j * diffusiveBlockLength constant scale n)
      (diffusiveBlockLength constant scale n)).div_const _
  have hpreimage (n : ℕ) :
      X n ⁻¹' G = {increment |
        ∀ j : Fin blocks,
          AdditivePath.blockSum
              (j * diffusiveBlockLength constant scale n)
              (diffusiveBlockLength constant scale n) increment /
              scale n ∈ Set.Ioo (lower j) (upper j)} := by
    ext increment
    simp only [X, G, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioo, Set.mem_ofPred_eq]
  simpa only [X, Z, G, Measure.map_apply (hX _) hG.measurableSet,
    hpreimage] using hbound

/-- The product-Gaussian probability in the finite-dimensional lower bound
factors into the one-dimensional interval probabilities used in Theorem 3,
Section 4 of A. A. Mogul'skii, *Small Deviations in a Space of Trajectories*
(DOI 10.1137/1119081). -/
private theorem measure_gaussianBlockBox_eq_prod
    {constant : ℝ} (hconstant : 0 < constant) {blocks : ℕ}
    (lower upper : Fin blocks → ℝ) :
    (Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z j => z j * Real.sqrt constant)
        (Set.univ.pi fun j => Set.Ioo (lower j) (upper j)) =
      ∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo (lower j / Real.sqrt constant)
            (upper j / Real.sqrt constant)) := by
  have hsqrt : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have hG : MeasurableSet
      (Set.univ.pi fun j : Fin blocks => Set.Ioo (lower j) (upper j)) :=
    MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo
  rw [Measure.map_apply (by fun_prop) hG]
  have hpreimage :
      (fun z : Fin blocks → ℝ => fun j => z j * Real.sqrt constant) ⁻¹'
          (Set.univ.pi fun j => Set.Ioo (lower j) (upper j)) =
        Set.univ.pi fun j =>
          (fun x : ℝ => x * Real.sqrt constant) ⁻¹'
            Set.Ioo (lower j) (upper j) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hpreimage, Measure.pi_pi]
  congr 1 with j
  apply measure_congr
  filter_upwards [] with x
  simp only [Set.mem_preimage, Set.mem_Ioo]
  exact propext ⟨fun h => ⟨(div_lt_iff₀ hsqrt).2 h.1,
      (lt_div_iff₀ hsqrt).2 h.2⟩,
    fun h => ⟨(div_lt_iff₀ hsqrt).1 h.1,
      (lt_div_iff₀ hsqrt).1 h.2⟩⟩

/-- Direct product form of the finite-dimensional open-box lower bound used
in Theorem 3, Section 4 of A. A. Mogul'skii, *Small Deviations in a Space of
Trajectories* (DOI 10.1137/1119081). -/
lemma prod_gaussian_Ioo_le_liminf_measure_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
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
                (j * diffusiveBlockLength constant scale n)
                (diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower j) (upper j)}) := by
  rw [← measure_gaussianBlockBox_eq_prod hconstant lower upper]
  exact measure_gaussianBlockBox_le_liminf ν hcentered hsecondMoment
    hscale hconstant blocks lower upper

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks
