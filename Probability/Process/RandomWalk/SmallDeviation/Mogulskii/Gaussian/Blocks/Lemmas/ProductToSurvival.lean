/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Gaussian.Interval
public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.Kernel.Killed.Partition
public import Probability.Process.RandomWalk.Kernel.Killed.Survival.Uniform
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.BlockScale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Path.PartitionTightness
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.PartitionEndpoints

/-!
# Lemmas for finite-reference Gaussian block survival

This module contains the two proof steps that transfer finite-dimensional
Gaussian endpoint bounds to killed-kernel survival for a finite family of
reference positions. The first consumes a common within-block control; the
second chooses one diffusive block scale for all references. They support the
uniform survival estimates in `FiniteReferenceSurvival.lean` and remain under
`Lemmas/` because they are specific steps of that proof chain.

The first lemma,
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.gaussianProduct_le_liminf_remainingMass_add_of_eventually_control`,
transfers the finite Gaussian product to the lower limit of the killed
survival mass, with the prescribed within-block error. The second,
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.exists_diffusiveBlockConstant_finset_gaussianProduct_le_liminf_remainingMass_add`,
chooses one $c>0$ so that for every reference $y$ in a finite set $F$, with
$a=\texttt{lower}$ and $b=\texttt{upper}$,
\[
  \prod_{j<m}\mathbb P\!\left(
    \frac{x_{y,j}-r}{\sqrt c}<Z<\frac{x_{y,j}+r}{\sqrt c}
  \right)
  \leq \liminf_{n\to\infty}
    K_{[s_n a,s_n b]}^{m\lfloor c s_n^2\rfloor}(s_n y,\mathbb R)
    +\operatorname{ofReal}(\eta).
\]
Here $Z\sim N(0,1)$, $x_{y,j}$ is the prescribed block target, and
$\eta>0$ is the common error; $K_{[s_n a,s_n b]}$ is the transition kernel
killed when the walk exits $[s_n a,s_n b]$.

These estimates occur in the proof of Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

/-- A prescribed common within-block control transfers the Gaussian endpoint
bound to killed-kernel survival from one normalized initial position.  Keeping
the control as an explicit hypothesis makes the chosen block scale reusable
for several initial positions. -/
lemma gaussianProduct_le_liminf_remainingMass_add_of_eventually_control
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper initial endpointMargin blockRadius tolerance : ℝ}
    (hinitial : initial ∈ Set.Icc lower upper)
    (hblockRadius : 0 < blockRadius)
    (target : ℕ → ℝ)
    (hmargin : ∀ k ≤ blocks,
      lower - initial + endpointMargin + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper - initial - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hcontrol : ∀ᶠ n in atTop, ∀ lower upper : ℕ → ℝ,
      (iidSequenceLaw ν) {increment | ∀ j < blocks,
          AdditivePath.displacement
              (j * diffusiveBlockLength constant scale n) increment /
              scale n ∈
            Set.Ioo (lower j + endpointMargin) (upper j - endpointMargin)} ≤
        (iidSequenceLaw ν) {increment | ∀ j < blocks,
            ∀ k ≤ diffusiveBlockLength constant scale n,
              AdditivePath.displacement
                  (j * diffusiveBlockLength constant scale n + k) increment ∈
                Set.Icc (scale n * lower j) (scale n * upper j)} +
          ENNReal.ofReal tolerance) :
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
  have hendpoint :=
    prod_gaussian_Ioo_le_liminf_measure_partitionEndpoints
      ν hν.1 hν.2 hscale hconstant hblockRadius target
      (fun _ => lower - initial + endpointMargin)
      (fun _ => upper - initial - endpointMargin) (by
        intro k hk
        have hm := hmargin k hk
        constructor <;> linarith)
  refine hendpoint.trans (Filter.liminf_le_liminf ?_)
  filter_upwards [hcontrol, _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale,
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_diffusiveBlockLength_pos hscale hconstant]
    with n hn hscalePos hlength
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
  have hc := hn (fun _ => lower - initial) (fun _ => upper - initial)
  rw [hevent, ← hkernel] at hc
  calc
    (iidSequenceLaw ν) {increment | ∀ k ≤ blocks,
        AdditivePath.displacement (k * diffusiveBlockLength constant scale n) increment /
            scale n ∈
          Set.Ioo (lower - initial + endpointMargin)
            (upper - initial - endpointMargin)} ≤
      (iidSequenceLaw ν) {increment | ∀ j < blocks,
        AdditivePath.displacement (j * diffusiveBlockLength constant scale n) increment /
            scale n ∈
          Set.Ioo (lower - initial + endpointMargin)
            (upper - initial - endpointMargin)} := by
        apply measure_mono
        intro increment hincrement j hj
        exact hincrement j hj.le
    _ ≤ _ := hc

/-- A finite family of normalized initial positions shares one diffusive block
constant.  Each reference may use its own deterministic target increments;
the within-block error and its scale are common to the whole family. -/
lemma exists_diffusiveBlockConstant_finset_gaussianProduct_le_liminf_remainingMass_add
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper endpointMargin blockRadius tolerance : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (htolerance : 0 < tolerance)
    (references : Finset ℝ) (target : ℝ → ℕ → ℝ)
    (hinitial : ∀ y ∈ references, y ∈ Set.Icc lower upper)
    (hmargin : ∀ y ∈ references, ∀ k ≤ blocks,
      lower - y + endpointMargin + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          upper - y - endpointMargin -
            (blocks : ℝ) * blockRadius) :
    ∃ constant > 0, ∀ y ∈ references,
      (∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target y j - blockRadius) / Real.sqrt constant)
              ((target y j + blockRadius) / Real.sqrt constant))) ≤
        atTop.liminf (fun n =>
          Kernel.remainingMass
              (killedIncrementKernel ν
                (Set.Icc (scale n * lower) (scale n * upper))
                measurableSet_Icc)
              (blocks * diffusiveBlockLength constant scale n)
              (scale n * y) +
            ENNReal.ofReal tolerance) := by
  obtain ⟨constant, hconstant, hcontrol⟩ :=
    exists_diffusiveBlockConstant_eventually_normalizedEndpoints_le_corridors_add
      ν hν hscale hblocks hendpointMargin htolerance
  refine ⟨constant, hconstant, ?_⟩
  intro y hy
  exact gaussianProduct_le_liminf_remainingMass_add_of_eventually_control
    ν hν hscale hconstant hblocks (hinitial y hy) hblockRadius
    (target y) (hmargin y hy) hcontrol
end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks
