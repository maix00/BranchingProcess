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
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.Lemmas.ProductParameters
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.Lemmas.ProductToSurvival

/-!
# Finite-reference Gaussian block survival

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.exists_diffusiveBlockConstant_eventually_uniform_remainingMass_of_finset`:
  a finite spatial cover and a strict Gaussian-product margin yield an
  eventual killed-kernel survival bound uniform over the initial interval.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.exists_eventually_finset_pos_remainingMass_zeroTarget`:
  for finitely many interior starts, some $c,p>0$ give survival mass
  at least $p$ for $\lfloor c x_n^2\rfloor$-length blocks eventually.

Writing $q_n=\lfloor c s_n^2\rfloor$ and $K_n$ for the walk killed outside
$[s_n a,s_n b]$, the second theorem gives
\[
  \exists c\in(0,1],\ p>0,\ N\in\mathbb N,\quad
  \forall n\geq N\ \forall y\in F,\quad
  p\leq K_n^{m q_n}(s_n y,\mathbb R),
\]
for a finite family $F\subseteq[a,b]$ whose points have a common strict
interior margin. The first theorem asserts that a finite cover $F$ and a
strict Gaussian-product margin $p+\eta<\prod_{j<m}\mathbb P(Z\in I_{y,j})$
for every $y\in F$ give some $c>0$ such that eventually
\[
  \forall x\in[a,b],\qquad p\leq K_n^{m q_n}(s_n x,\mathbb R).
\]
Here $I_{y,j}$ is the Gaussian target interval for block $j$ and $\eta>0$
is the within-block error.

The diffusive block length used in the finite-dimensional lower bound is
chosen before the reference point.  Consequently a finite family of initial
positions can share one block scale, as required by the uniform killed-kernel
blocking argument.

This isolates the finite-reference survival step in the proof of Theorem 3,
Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory Set

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks



/-- The common-scale finite-reference estimate feeds directly into the
uniform survival comparison.  Once a number lies strictly below every finite
Gaussian product after paying the common error, it eventually bounds survival
from every normalized point of the original interval. -/
theorem exists_diffusiveBlockConstant_eventually_uniform_remainingMass_of_finset
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper coverMargin endpointMargin blockRadius tolerance : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (htolerance : 0 < tolerance)
    (references : Finset ℝ) (target : ℝ → ℕ → ℝ)
    (hcover : ∀ x ∈ Set.Icc lower upper,
      ∃ y ∈ references, |x - y| ≤ coverMargin)
    (hinitial : ∀ y ∈ references,
      y ∈ Set.Icc (lower + coverMargin) (upper - coverMargin))
    (hmargin : ∀ y ∈ references, ∀ k ≤ blocks,
      lower + coverMargin - y + endpointMargin +
            (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          upper - coverMargin - y - endpointMargin -
            (blocks : ℝ) * blockRadius) :
    ∃ constant > 0, ∀ lowerBound : ENNReal,
      (∀ y ∈ references,
        lowerBound + ENNReal.ofReal tolerance <
          ∏ j : Fin blocks,
            gaussianReal 0 1
              (Set.Ioo
                ((target y j - blockRadius) / Real.sqrt constant)
                ((target y j + blockRadius) / Real.sqrt constant))) →
      ∀ᶠ n in atTop, ∀ x : Set.Icc lower upper,
        lowerBound ≤ Kernel.remainingMass
          (killedIncrementKernel ν
            (Set.Icc (scale n * lower) (scale n * upper))
            measurableSet_Icc)
          (blocks * diffusiveBlockLength constant scale n)
          (scale n * x) := by
  obtain ⟨constant, hconstant, href⟩ :=
    exists_diffusiveBlockConstant_finset_gaussianProduct_le_liminf_remainingMass_add
      ν hν hscale hblocks hendpointMargin hblockRadius htolerance
      references target hinitial hmargin
  refine ⟨constant, hconstant, ?_⟩
  intro lowerBound hgap
  exact eventually_forall_le_remainingMass_killedIncrementKernel_Icc_of_finset_liminf
    ν lower upper coverMargin references scale
      (fun n => blocks * diffusiveBlockLength constant scale n)
      lowerBound (ENNReal.ofReal tolerance)
      (fun y => ∏ j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            ((target y j - blockRadius) / Real.sqrt constant)
            ((target y j + blockRadius) / Real.sqrt constant)))
      (by simp) ((_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale).mono fun _ hn => hn.le)
      hcover href hgap

/-- A finite family of normalized starting points with a common strict
interior margin eventually shares one positive killed-kernel survival bound.
The block constant, maximal-inequality error, and numerical lower bound are
chosen together, so no circular error hypothesis remains.  Boundary starting
points require a separate entrance estimate and are deliberately excluded
from this statement. -/
theorem exists_eventually_finset_pos_remainingMass_zeroTarget
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {endpointMargin blockRadius : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {lower upper : ℝ} (references : Finset ℝ)
    (hinitial : ∀ y ∈ references, y ∈ Set.Icc lower upper)
    (hmargin : ∀ y ∈ references,
      lower - y + endpointMargin + (blocks : ℝ) * blockRadius < 0 ∧
        0 < upper - y - endpointMargin -
          (blocks : ℝ) * blockRadius) :
    ∃ constant > 0, constant ≤ 1 ∧
      ∃ lowerBound : ENNReal, 0 < lowerBound ∧
        ∀ᶠ n in atTop, ∀ y ∈ references,
          lowerBound ≤ Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * lower) (scale n * upper))
              measurableSet_Icc)
            (blocks * diffusiveBlockLength constant scale n)
            (scale n * y) := by
  obtain ⟨constant, hconstant, hconstantOne, error, herror,
      lowerBound, hlowerBound, hgap⟩ :=
    Gaussian.Blocks.exists_constant_error_lowerBound_lt_gaussianProduct
      hendpointMargin hblockRadius hblocks
  have hcontrol :=
    eventually_normalizedEndpoints_le_corridors_add_explicitError
      ν hν hscale hconstant hendpointMargin herror blocks
  let errorMass := ENNReal.ofReal
    (blocks * (constant / endpointMargin ^ 2 + error))
  let gaussianBound := ∏ _j : Fin blocks,
    gaussianReal 0 1
      (Set.Ioo
        (-blockRadius / Real.sqrt constant)
        (blockRadius / Real.sqrt constant))
  have hliminf : ∀ y ∈ references,
      gaussianBound ≤ atTop.liminf (fun n =>
        Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * lower) (scale n * upper))
              measurableSet_Icc)
            (blocks * diffusiveBlockLength constant scale n)
            (scale n * y) + errorMass) := by
    intro y hy
    simpa [gaussianBound, errorMass] using
      (gaussianProduct_le_liminf_remainingMass_add_of_eventually_control
        ν hν hscale hconstant hblocks (hinitial y hy) hblockRadius
        (fun _ => 0) (by
          intro k hk
          simpa using hmargin y hy) hcontrol)
  have hreference : ∀ y ∈ references, ∀ᶠ n in atTop,
      lowerBound ≤ Kernel.remainingMass
        (killedIncrementKernel ν
          (Set.Icc (scale n * lower) (scale n * upper)) measurableSet_Icc)
        (blocks * diffusiveBlockLength constant scale n)
        (scale n * y) := by
    intro y hy
    have hgap' : lowerBound + errorMass < gaussianBound := by
      simpa [gaussianBound, errorMass] using hgap
    have hstrict : lowerBound + errorMass < atTop.liminf (fun n =>
        Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * lower) (scale n * upper))
              measurableSet_Icc)
            (blocks * diffusiveBlockLength constant scale n)
            (scale n * y) + errorMass) :=
      hgap'.trans_le (hliminf y hy)
    have herrorFinite : errorMass ≠ ⊤ := by
      exact ENNReal.ofReal_ne_top
    filter_upwards [eventually_lt_of_lt_liminf hstrict] with n hn
    exact ((ENNReal.add_lt_add_iff_right herrorFinite).1 hn).le
  refine ⟨constant, hconstant, hconstantOne,
    lowerBound, hlowerBound, ?_⟩
  exact references.eventually_all.2 hreference

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks
