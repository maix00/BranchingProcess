module

public import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.CLT
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.BlockScale

/-!
# Diffusive block endpoint adapters for Mogulskii estimates

The central limit theorem itself lives in the Donsker layer.  This file only
connects it to the subdiffusive block scale used by Mogulskii's proof.
-/

open Filter MeasureTheory

@[expose] public section
open scoped BigOperators

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

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
            partialSum (diffusiveBlockLength constant scale n) increment *
          (Real.sqrt (diffusiveBlockLength constant scale n) / scale n))
      atTop (fun x => x * Real.sqrt constant)
      (fun _ => independentIncrementLaw ν) (gaussianReal 0 1) := by
  have hnormalized :=
    (tendstoInDistribution_normalizedPartialSum ν hcentered hsecondMoment).comp_tendsto
      (hscale.tendsto_diffusiveBlockLength_atTop hconstant)
  have hcoefficient : TendstoInMeasure (independentIncrementLaw ν)
      (fun n (_ : ℕ → ℝ) =>
        Real.sqrt (diffusiveBlockLength constant scale n) / scale n)
      atTop (fun _ => Real.sqrt constant) := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => by fun_prop)
    filter_upwards [] with increment
    exact hscale.tendsto_sqrt_diffusiveBlockLength_div hconstant
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
        partialSum (diffusiveBlockLength constant scale n) increment /
          scale n)
      atTop (fun x => x * Real.sqrt constant)
      (fun _ => independentIncrementLaw ν) (gaussianReal 0 1) := by
  apply (tendstoInDistribution_diffusiveBlockEndpoint ν hcentered
    hsecondMoment hscale hconstant).congr_eventually
  · filter_upwards [hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant]
      with n hnScale hnBlock
    filter_upwards [] with increment
    have hsqrt : Real.sqrt (diffusiveBlockLength constant scale n) ≠ 0 :=
      Real.sqrt_ne_zero'.2 (by exact_mod_cast hnBlock)
    field_simp [hsqrt, hnScale.ne']
  · intro n
    exact (partialSum_measurable _).div_const _ |>.aemeasurable

end ProbabilityTheory.RandomWalk
