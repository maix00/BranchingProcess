/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.CLT
public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale

/-!
# Diffusive Gaussian block endpoint adapters for Mogulskii estimates

Let $b_n=\lfloor c x_n^2\rfloor$ with $c>0$ and $x_n\to\infty$. The public
theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.tendstoInDistribution_diffusiveBlockEndpoint`:
  the product of $\frac{S_{b_n}}{\sqrt{b_n}}$ and
  $\frac{\sqrt{b_n}}{x_n}$ converges in law to
  $\sqrt c Z$, where $Z$ is standard Gaussian. The separate factors also
  define the expression when $b_n=0$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.tendstoInDistribution_partialSum_diffusiveBlock_div_scale`:
  the direct quotient $\frac{S_{b_n}}{x_n}$ converges in law to $\sqrt c Z$.

The central limit theorem itself lives in the Donsker layer. These are the
single-block inputs used in the proof of Mogul'skii, *Small Deviations in a
Space of Trajectories*, Theorem 3, Section 4, p. 764 of the 1974 Russian original
(DOI 10.1137/1119081).


The original bibliography is A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. -/

open Filter MeasureTheory

@[expose] public section
open scoped BigOperators

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian

/-- The normalized endpoint of a diffusive block converges to a Gaussian
scaled by the square root of the block constant.  The two displayed factors
are kept separate so the statement is valid even at the finitely many
indices where the rounded block length can vanish. -/
theorem tendstoInDistribution_diffusiveBlockEndpoint
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    TendstoInDistribution
      (fun n increment =>
        (Real.sqrt (diffusiveBlockLength constant scale n))⁻¹ *
            AdditivePath.displacement (diffusiveBlockLength constant scale n) increment *
          (Real.sqrt (diffusiveBlockLength constant scale n) / scale n))
      atTop (fun x => x * Real.sqrt constant)
      (fun _ => iidSequenceLaw ν) (gaussianReal 0 1) := by
  have hnormalized :=
    (tendstoInDistribution_normalizedPartialSum ν hcentered hsecondMoment).comp_tendsto
      (_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_diffusiveBlockLength_atTop hscale hconstant)
  have hcoefficient : TendstoInMeasure (iidSequenceLaw ν)
      (fun n (_ : ℕ → ℝ) =>
        Real.sqrt (diffusiveBlockLength constant scale n) / scale n)
      atTop (fun _ => Real.sqrt constant) := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => by fun_prop)
    filter_upwards [] with increment
    exact _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_sqrt_diffusiveBlockLength_div hscale hconstant
  exact hnormalized.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun pair : ℝ × ℝ => pair.1 * pair.2) (by fun_prop)
    hcoefficient (fun _ => by fun_prop)

/-- After discarding the finitely many indices where rounding can produce a
zero block, the preceding product is the usual block endpoint divided by the
Mogulskii spatial scale. -/
theorem tendstoInDistribution_partialSum_diffusiveBlock_div_scale
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    TendstoInDistribution
      (fun n increment =>
        AdditivePath.displacement (diffusiveBlockLength constant scale n) increment /
          scale n)
      atTop (fun x => x * Real.sqrt constant)
      (fun _ => iidSequenceLaw ν) (gaussianReal 0 1) := by
  apply (tendstoInDistribution_diffusiveBlockEndpoint ν hcentered
    hsecondMoment hscale hconstant).congr_eventually
  · filter_upwards [_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale,
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_diffusiveBlockLength_pos hscale hconstant]
      with n hnScale hnBlock
    filter_upwards [] with increment
    have hsqrt : Real.sqrt (diffusiveBlockLength constant scale n) ≠ 0 :=
      Real.sqrt_ne_zero'.2 (by exact_mod_cast hnBlock)
    field_simp [hsqrt, hnScale.ne']
  · intro n
    exact (displacement_measurable _).div_const _ |>.aemeasurable

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian
