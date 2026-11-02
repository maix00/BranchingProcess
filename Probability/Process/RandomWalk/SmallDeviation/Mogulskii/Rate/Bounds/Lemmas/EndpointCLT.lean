/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Basic.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Probability.Process.Brownian.SmallDeviation.Range.UpperRate
import Probability.Process.RandomWalk.Kernel.Killed.Basic
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
import Analysis.Asymptotics.Scale.Block.Diffusive
import Probability.Sequence.IID.Basic
import Probability.ConvergenceInDistribution.Basic
import Probability.Process.RandomWalk.FunctionalLimit.Normal.FiniteDimensional.CentralLimitTheorem
import Probability.Process.RandomWalk.Kernel.Killed.Survival.Blocking
import Probability.Process.RandomWalk.Path.Basic
import Probability.Process.RandomWalk.Path.Block.Oscillation
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.UpperBound
import Probability.Sequence.Block
/-!
# Endpoint-CLT block estimate

## Internal proof declarations

- `tendstoInDistribution_diffusiveBlockEndpoint` and `tendstoInDistribution_partialSum_diffusiveBlock_div_scale`: endpoint and partial-sum forms of the diffusive block limit.
- `eventually_uniform_killedBlock_remainingMass_le_of_endpointCLT`: the endpoint central limit estimate gives a uniform killed-block survival bound over every starting point in the interval.


These declarations form a one-use proof stage for `Upper.lean` in the
finite-variance horizontal-tube estimate of A. A. Mogul'skii, Theorem 3,
Section 4, p. 764, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.

For diffusive block length $m_n=\lfloor c s_n^2\rfloor$, the endpoint
converges as $S_{m_n}/s_n\Rightarrow N(0,c)$. Thus, if
$\mathbb P\{N(0,c)\in[-(u-\ell),u-\ell]\}<q$, then eventually every
starting point $x\in[\ell s_n,u s_n]$ has killed-block remaining mass at
most $q$.

-/

section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/- The single-block endpoint limit is a local scaling consequence of the
normalized partial-sum CLT. It is used only in this upper-bound argument. -/
lemma tendstoInDistribution_diffusiveBlockEndpoint
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    TendstoInDistribution
      (fun n increment =>
        (Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n))⁻¹ *
            AdditivePath.displacement (Asymptotics.diffusiveBlockLength constant scale n) increment *
          (Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) / scale n))
      atTop (fun x => x * Real.sqrt constant)
      (fun _ => iidSequenceLaw ν) (gaussianReal 0 1) := by
  have hnormalized :=
    (tendstoInDistribution_normalizedPartialSum ν hcentered hsecondMoment).comp_tendsto
      (_root_.Asymptotics.IsSmallDeviationScale.tendsto_diffusiveBlockLength_atTop hscale hconstant)
  have hcoefficient : TendstoInMeasure (iidSequenceLaw ν)
      (fun n (_ : ℕ → ℝ) =>
        Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) / scale n)
      atTop (fun _ => Real.sqrt constant) := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => by fun_prop)
    filter_upwards [] with increment
    exact _root_.Asymptotics.IsSmallDeviationScale.tendsto_sqrt_diffusiveBlockLength_div hscale hconstant
  exact hnormalized.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun pair : ℝ × ℝ => pair.1 * pair.2) (by fun_prop)
    hcoefficient (fun _ => by fun_prop)

lemma tendstoInDistribution_partialSum_diffusiveBlock_div_scale
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    TendstoInDistribution
      (fun n increment =>
        AdditivePath.displacement (Asymptotics.diffusiveBlockLength constant scale n) increment /
          scale n)
      atTop (fun x => x * Real.sqrt constant)
      (fun _ => iidSequenceLaw ν) (gaussianReal 0 1) := by
  apply (tendstoInDistribution_diffusiveBlockEndpoint ν hcentered
    hsecondMoment hscale hconstant).congr_eventually
  · filter_upwards [_root_.Asymptotics.IsSmallDeviationScale.eventually_pos hscale,
      _root_.Asymptotics.IsSmallDeviationScale.eventually_diffusiveBlockLength_pos hscale hconstant]
      with n hnScale hnBlock
    filter_upwards [] with increment
    have hsqrt : Real.sqrt (Asymptotics.diffusiveBlockLength constant scale n) ≠ 0 :=
      Real.sqrt_ne_zero'.2 (by exact_mod_cast hnBlock)
    field_simp [hsqrt, hnScale.ne']
  · intro n
    exact (displacement_measurable _).div_const _ |>.aemeasurable


/-- A strict upper bound on the limiting Gaussian endpoint mass gives an
eventual uniform upper bound on every row of the interval-killed kernel,
when the source state ranges over the whole allowed interval. -/
lemma eventually_uniform_killedBlock_remainingMass_le_of_endpointCLT
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (lower upper constant q : ℝ)
    (hconstant : 0 < constant)
    (hgaussian : (gaussianReal 0 1).map
        (fun z : ℝ => z * Real.sqrt constant)
        (Set.Icc (-(upper - lower)) (upper - lower)) < ENNReal.ofReal q) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : Set.Icc (lower * scale n) (upper * scale n),
        Kernel.remainingMass
          (killedIncrementKernelOn ν
            (Set.Icc (lower * scale n) (upper * scale n)) measurableSet_Icc)
          (Asymptotics.diffusiveBlockLength constant scale n) x ≤ ENNReal.ofReal q := by
  let block : ℕ → ℕ := Asymptotics.diffusiveBlockLength constant scale
  let endpoint : ℕ → ENNReal := fun n =>
    (iidSequenceLaw ν).map
      (fun increment => AdditivePath.displacement (block n) increment / scale n)
      (Set.Icc (-(upper - lower)) (upper - lower))
  have hclt := tendstoInDistribution_partialSum_diffusiveBlock_div_scale
    ν hcentered hsecondMoment hscale hconstant
  have hport : atTop.limsup endpoint ≤
      (gaussianReal 0 1).map (fun z : ℝ => z * Real.sqrt constant)
        (Set.Icc (-(upper - lower)) (upper - lower)) := by
    simpa only [endpoint, block] using
      hclt.limsup_measure_map_le_of_isClosed isClosed_Icc
  have hbounded : Filter.IsBoundedUnder (· ≤ ·) atTop endpoint := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      have hmap : (iidSequenceLaw ν).map
          (fun increment => AdditivePath.displacement (block n) increment / scale n)
          Set.univ = 1 := by
        rw [Measure.map_apply
          ((displacement_measurable (block n)).div_const (scale n))
          MeasurableSet.univ]
        simp
      calc
        endpoint n ≤ (iidSequenceLaw ν).map
            (fun increment => AdditivePath.displacement (block n) increment / scale n) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := hmap
  have hendpoint : ∀ᶠ n : ℕ in atTop, endpoint n < ENNReal.ofReal q :=
    eventually_lt_of_limsup_lt (hport.trans_lt hgaussian) hbounded
  filter_upwards [hendpoint, _root_.Asymptotics.IsSmallDeviationScale.eventually_pos hscale,
      _root_.Asymptotics.IsSmallDeviationScale.eventually_diffusiveBlockLength_pos hscale hconstant]
    with n hnEndpoint hnScale hnBlock
  intro x
  rw [killedIncrementKernelOn_remainingMass_eq_iidSequenceLaw
    ν (Set.Icc (lower * scale n) (upper * scale n)) measurableSet_Icc
    (block n) x]
  have hsub : iidSequenceLaw ν
      {increment | StaysIn (Set.Icc (lower * scale n) (upper * scale n))
        (block n) (x : ℝ) increment} ≤ endpoint n := by
    dsimp [endpoint]
    rw [Measure.map_apply
      ((displacement_measurable (block n)).div_const (scale n))
      measurableSet_Icc]
    unfold iidSequenceLaw
    apply measure_mono
    intro increment hstay
    have hclosed := (staysIn_Icc_iff_inClosedInterval
      (lower * scale n) (upper * scale n) (block n) (x : ℝ)
      x.property increment).mp hstay
    have hendpoint : (x : ℝ) + AdditivePath.displacement (block n) increment ∈
        Set.Icc (lower * scale n) (upper * scale n) := by
      have hlast := hclosed ⟨block n, Nat.lt_succ_self (block n)⟩
      simpa [InClosedInterval, InWindows, history_eq_fromIncrements,
        AdditivePath.fromIncrements] using hlast
    let normalizedStart : ℝ := (x : ℝ) / scale n
    have hnormalizedStart : normalizedStart ∈ Set.Icc lower upper := by
      constructor
      · apply (le_div_iff₀ hnScale).2
        simpa [normalizedStart, mul_comm] using x.property.1
      · apply (div_le_iff₀ hnScale).2
        simpa [normalizedStart, mul_comm] using x.property.2
    have hsumLower : lower - normalizedStart ≤
        AdditivePath.displacement (block n) increment / scale n := by
      have h := div_le_div_of_nonneg_right hendpoint.1 hnScale.le
      have h' : lower ≤ normalizedStart +
          AdditivePath.displacement (block n) increment / scale n := by
        calc
          lower = (lower * scale n) / scale n := by
            field_simp [hnScale.ne']
          _ ≤ ((x : ℝ) + AdditivePath.displacement (block n) increment) / scale n := h
          _ = normalizedStart + AdditivePath.displacement (block n) increment / scale n := by
            simp [normalizedStart, add_div]
      linarith
    have hsumUpper : AdditivePath.displacement (block n) increment / scale n ≤
        upper - normalizedStart := by
      have h := div_le_div_of_nonneg_right hendpoint.2 hnScale.le
      have h' : normalizedStart +
          AdditivePath.displacement (block n) increment / scale n ≤ upper := by
        calc
          normalizedStart + AdditivePath.displacement (block n) increment / scale n =
              ((x : ℝ) + AdditivePath.displacement (block n) increment) / scale n := by
            simp [normalizedStart, add_div]
          _ ≤ (upper * scale n) / scale n := h
          _ = upper := by field_simp [hnScale.ne']
      linarith
    have hsum : AdditivePath.displacement (block n) increment / scale n ∈
        Set.Icc (-(upper - lower)) (upper - lower) := by
      constructor
      · calc
          -(upper - lower) ≤ lower - normalizedStart := by
            have := hnormalizedStart.2
            linarith
          _ ≤ AdditivePath.displacement (block n) increment / scale n := hsumLower
      · calc
          AdditivePath.displacement (block n) increment / scale n ≤ upper - normalizedStart :=
            hsumUpper
          _ ≤ upper - lower := by
            have := hnormalizedStart.1
            linarith
    exact hsum
  exact hsub.trans (le_of_lt hnEndpoint)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
