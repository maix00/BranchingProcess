/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Killed.Return.Comparison
public import Probability.Distributions.Moments.Real
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.BlockScale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.ReturnKernel

/-!
# Uniform Gaussian block bounds for return kernels

A finite cover of the normalized return interval and a positive Gaussian block
product margin yield an eventual one-block lower bound, uniform over every
starting point in the scaled interval. The block-product estimate is the
finite-dimensional lower-bound step in Theorem 3, Section 4 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.

The public declaration in `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks` is:

- `eventually_uniform_returnKernel_of_finset_gaussianProduct`: a finite
  Gaussian reference family with a strict product margin gives an eventual
  lower bound on the return kernel, uniformly over its normalized interval.

Write $q_n=\operatorname{diffusiveBlockLength}(C,s,n)$. If the finite
Gaussian products exceed $p+\operatorname{ofReal}(m(C/\rho^2+e))$ at every
reference point and those points form the prescribed cover, then eventually
\[
  p\leq K_{[s_n a,s_n b]}^{m q_n}
       (s_n x,[s_n c,s_n d])\qquad\text{for every }x\in[c,d].
\]
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

/-- A finite collection of Gaussian return estimates, all using the same
block scale and error, yields an eventual return-kernel lower bound uniform
over the full normalized return interval. -/
theorem eventually_uniform_returnKernel_of_finset_gaussianProduct
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscaleNonneg : ∀ n, 0 ≤ scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {outerLower outerUpper returnLower returnUpper coverMargin : ℝ}
    {endpointMargin blockRadius error : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius) (herror : 0 < error)
    (references : Finset ℝ) (target : ℝ → ℕ → ℝ)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ coverMargin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + coverMargin)
        (returnUpper - coverMargin))
    (houter : ∀ y ∈ references,
      y ∈ Set.Icc (outerLower + coverMargin)
        (outerUpper - coverMargin))
    (hstartMargin : ∀ y ∈ references, ∀ k < blocks,
      outerLower + coverMargin - y + endpointMargin +
            (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range k, target y j ∧
        ∑ j ∈ Finset.range k, target y j <
          outerUpper - coverMargin - y - endpointMargin -
            (blocks : ℝ) * blockRadius)
    (hfinalMargin : ∀ y ∈ references,
      returnLower + coverMargin - y + (blocks : ℝ) * blockRadius <
          ∑ j ∈ Finset.range blocks, target y j ∧
        ∑ j ∈ Finset.range blocks, target y j <
          returnUpper - coverMargin - y -
            (blocks : ℝ) * blockRadius)
    (lowerBound : ENNReal)
    (hgap : ∀ y ∈ references,
      lowerBound + ENNReal.ofReal
          (blocks * (constant / endpointMargin ^ 2 + error)) <
        ∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target y j - blockRadius) / Real.sqrt constant)
              ((target y j + blockRadius) / Real.sqrt constant))) :
    ∀ᶠ n in atTop, ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale n * outerLower) (scale n * outerUpper)) measurableSet_Icc
        (Set.Icc (scale n * returnLower) (scale n * returnUpper)) measurableSet_Icc
        (blocks * diffusiveBlockLength constant scale n)
        ⟨scale n * x, by
          constructor <;> nlinarith [x.property.1, x.property.2,
            hscaleNonneg n]⟩ univ := by
  let errorMass := ENNReal.ofReal
    (blocks * (constant / endpointMargin ^ 2 + error))
  let referenceBound : ℝ → ENNReal := fun y => ∏ j : Fin blocks,
    gaussianReal 0 1
      (Set.Ioo
        ((target y j - blockRadius) / Real.sqrt constant)
        ((target y j + blockRadius) / Real.sqrt constant))
  have hliminf : ∀ (y : ℝ) (hy : y ∈ references),
      referenceBound y ≤ atTop.liminf (fun n =>
        returnKernel ν
          (Set.Icc (scale n * (outerLower + coverMargin))
            (scale n * (outerUpper - coverMargin))) measurableSet_Icc
          (Set.Icc (scale n * (returnLower + coverMargin))
            (scale n * (returnUpper - coverMargin))) measurableSet_Icc
          (blocks * diffusiveBlockLength constant scale n)
          ⟨scale n * y, by
            constructor <;> nlinarith [(hreference y hy).1,
              (hreference y hy).2, hscaleNonneg n]⟩ univ + errorMass) := by
    intro y hy
    simpa only [referenceBound, errorMass] using
      (gaussianProduct_le_liminf_returnKernel_add
        ν hν hscale hscaleNonneg hconstant hblocks
        (houter y hy) (hreference y hy) hendpointMargin hblockRadius herror
        (target y) (hstartMargin y hy) (hfinalMargin y hy))
  exact eventually_forall_le_returnKernel_Icc_apply_univ_of_finset_liminf
    ν outerLower outerUpper returnLower returnUpper coverMargin references
    scale (fun n => blocks * diffusiveBlockLength constant scale n)
    lowerBound errorMass referenceBound ENNReal.ofReal_ne_top hscaleNonneg
    hcover hreference hliminf (by
      intro y hy
      simpa only [referenceBound, errorMass] using hgap y hy)


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks
