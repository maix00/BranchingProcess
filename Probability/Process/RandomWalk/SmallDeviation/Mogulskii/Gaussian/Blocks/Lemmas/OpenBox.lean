/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Path.Block.Law.Basic
import Analysis.Asymptotics.Scale.Block.Diffusive
import Probability.ConvergenceInDistribution.Basic
import Probability.Distributions.Stable.Gaussian.Basic
import Probability.Sequence.IID.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import Probability.Process.RandomWalk.FunctionalLimit.FiniteDimensional.IndependentBlocks
import Probability.Distributions.Stable.Attraction.Normal.Basic
import Probability.ConvergenceInDistribution.Portmanteau

/-!
# Proof steps for the Gaussian finite-dimensional block lower bound

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.measure_gaussianBlockBox_le_liminf`:
  for the same assumptions and a finite open box $G=\prod_{j<m}(a_j,b_j)$,
  \[
    (\otimes_{j<m}N(0,c))(G)\leq
      \liminf_{n\to\infty}\mathbb P_\nu((B_{n,j})_{j<m}\in G).
  \]
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.measure_gaussianBlockBox_eq_prod`:
  when $c>0$, the Gaussian probability of the scaled finite box factors as
  \[
    (\otimes_{j<m}N(0,1))\{z:(\sqrt c\,z_j)_{j<m}\in G\}
      =\prod_{j<m}N(0,1)((a_j/\sqrt c,b_j/\sqrt c)).
  \]

The finite diffusive block limit is private to this module; it specializes
`ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockSums`.
For the discrete variables in these statements,
$q_n=\operatorname{diffusiveBlockLength}(c,s,n)$ and
$B_{n,j}=\frac{S_{(j+1)q_n}-S_{jq_n}}{s_n}$, where
$S_k=\sum_{i<k}\xi_i$ and $\xi_i$ are the IID increments. The lemmas are
finite-dimensional inputs to the block argument; their generic convergence,
Portmanteau, and product-measure interfaces remain at their respective owners.

These are finite-dimensional inputs for the block argument in Theorem 3,
Section 4, p. 764 of the 1974 Russian original by A. A. Mogul'skii, “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081. The endpoint CLT comes from the Donsker
layer; this file does not assert tightness in path space.
-/

open Filter MeasureTheory Set

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

/-- Any fixed finite vector of consecutive diffusive block sums converges to
independent centered Gaussian increments. This is the finite-dimensional
block limit used in Theorem 3, Section 4, p. 764 of A. A. Mogul'skii,
*Small Deviations in a Space of Trajectories* (DOI 10.1137/1119081). -/
private lemma tendstoInDistribution_diffusiveBlockSums
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ) :
    TendstoInDistribution
      (fun n increment (j : Fin blocks) =>
        let length := Asymptotics.diffusiveBlockLength constant scale n
        AdditivePath.blockSum (j * length) length increment / scale n)
      atTop
      (fun z (j : Fin blocks) => z j * Real.sqrt constant)
      (fun _ => iidSequenceLaw ν)
      (Measure.pi fun _ : Fin blocks => gaussianReal 0 1) := by
  let normalization : ℕ → ℝ := fun n => Real.sqrt n
  let length : ℕ → ℕ → ℕ :=
    fun n _ => Asymptotics.diffusiveBlockLength constant scale n
  let ratio : Fin blocks → ℝ := fun _ => Real.sqrt constant
  let shift : Fin blocks → ℝ := fun _ => 0
  have hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0) := by
    simpa [normalization] using
      ProbabilityTheory.isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_unitSecondMoment
        ν ⟨hcentered, hsecondMoment⟩
  have hlength (j : Fin blocks) :
      Tendsto (fun n => length n j.val) atTop atTop := by
    have hlength' :=
      Asymptotics.tendsto_diffusiveBlockLength_atTop_of_tendsto_atTop
        hscale hconstant
    simpa [length] using hlength'
  have hscalePos : ∀ᶠ n : ℕ in atTop, scale n ≠ 0 := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0)] with n hn
    exact hn.ne'
  have hratio (j : Fin blocks) :
      Tendsto (fun n => normalization (length n j.val) / scale n)
        atTop (nhds (ratio j)) := by
    simpa [normalization, length, ratio] using
      _root_.Asymptotics.tendsto_sqrt_diffusiveBlockLength_div_of_tendsto_atTop
        hscale hconstant
  have hcenter (j : Fin blocks) :
      Tendsto (fun n => (0 : ℝ) / scale n) atTop (nhds (shift j)) := by
    simp [shift]
  have hblocks :=
    ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockSums
      hDOA blocks length scale ratio shift hlength hscalePos hratio hcenter
  have hstart (n : ℕ) (j : Fin blocks) :
      Combinatorics.Sequence.blockStart (length n) j.val =
        j.val * Asymptotics.diffusiveBlockLength constant scale n := by
    simp [length, Combinatorics.Sequence.blockStart_const]
  simpa [length, ratio, shift, hstart, mul_comm] using hblocks

/-- The limiting product-Gaussian probability of a finite open box is a
lower bound for the liminf of the corresponding normalized block-vector
probabilities. This is the open-set lower bound applied to the finite block
limit in Theorem 3, Section 4 of A. A. Mogul'skii, *Small Deviations in a
Space of Trajectories* (DOI 10.1137/1119081). -/
lemma measure_gaussianBlockBox_le_liminf
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {constant : ℝ} (hconstant : 0 < constant) (blocks : ℕ)
    (lower upper : Fin blocks → ℝ) :
    (Measure.pi fun _ : Fin blocks => gaussianReal 0 1).map
        (fun z j => z j * Real.sqrt constant)
        (Set.univ.pi fun j => Set.Ioo (lower j) (upper j)) ≤
      atTop.liminf (fun n =>
        (iidSequenceLaw ν) {increment |
          ∀ j : Fin blocks,
            AdditivePath.blockSum
                (j * Asymptotics.diffusiveBlockLength constant scale n)
                (Asymptotics.diffusiveBlockLength constant scale n) increment /
                scale n ∈ Set.Ioo (lower j) (upper j)}) := by
  let X : ℕ → (ℕ → ℝ) → (Fin blocks → ℝ) := fun n increment j =>
    AdditivePath.blockSum
        (j * Asymptotics.diffusiveBlockLength constant scale n)
        (Asymptotics.diffusiveBlockLength constant scale n) increment / scale n
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
      (j * Asymptotics.diffusiveBlockLength constant scale n)
      (Asymptotics.diffusiveBlockLength constant scale n)).div_const _
  have hpreimage (n : ℕ) :
      X n ⁻¹' G = {increment |
        ∀ j : Fin blocks,
          AdditivePath.blockSum
              (j * Asymptotics.diffusiveBlockLength constant scale n)
              (Asymptotics.diffusiveBlockLength constant scale n) increment /
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
lemma measure_gaussianBlockBox_eq_prod
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks
