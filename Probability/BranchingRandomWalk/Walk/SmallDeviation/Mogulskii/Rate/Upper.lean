/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Walk.Kernel.Killed
public import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Blocking
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.CLT
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.BlockScale

/-!
# Uniform block upper bounds from the endpoint CLT

For a walk that stays in a fixed-width interval, its displacement over a
complete block must lie in an interval whose length is at most twice the
corridor width.  The diffusive endpoint CLT therefore gives a uniform
strictly subunit upper bound for one block whenever the limiting Gaussian
puts less mass on that displacement interval than the chosen bound.  Kernel
blocking then gives an exponential upper bound over arbitrary durations.

This is a non-sharp upper estimate.  The sharp Mogulskii constant requires a
path-level killed-block estimate; endpoint control alone cannot give that
constant.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A strict upper bound on the limiting Gaussian endpoint mass gives an
eventual uniform upper bound on every row of the interval-killed kernel,
when the source state ranges over the whole allowed interval. -/
theorem eventually_uniform_killedBlock_remainingMass_le_of_endpointCLT
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (lower upper constant q : ℝ) (_hlowerUpper : lower < upper)
    (hconstant : 0 < constant) (_hq : 0 < q) (_hqOne : q < 1)
    (hgaussian : (gaussianReal 0 1).map
        (fun z : ℝ => z * Real.sqrt constant)
        (Set.Icc (-(upper - lower)) (upper - lower)) < ENNReal.ofReal q) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : Set.Icc (lower * scale n) (upper * scale n),
        Kernel.remainingMass
          (killedIncrementKernelOn ν
            (Set.Icc (lower * scale n) (upper * scale n)) measurableSet_Icc)
          (diffusiveBlockLength constant scale n) x ≤ ENNReal.ofReal q := by
  let block : ℕ → ℕ := diffusiveBlockLength constant scale
  let endpoint : ℕ → ENNReal := fun n =>
    (independentIncrementLaw ν).map
      (fun increment => partialSum (block n) increment / scale n)
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
      have hmap : (independentIncrementLaw ν).map
          (fun increment => partialSum (block n) increment / scale n)
          Set.univ = 1 := by
        rw [Measure.map_apply
          ((partialSum_measurable (block n)).div_const (scale n))
          MeasurableSet.univ]
        simp
      calc
        endpoint n ≤ (independentIncrementLaw ν).map
            (fun increment => partialSum (block n) increment / scale n) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := hmap
  have hendpoint : ∀ᶠ n : ℕ in atTop, endpoint n < ENNReal.ofReal q :=
    eventually_lt_of_limsup_lt (hport.trans_lt hgaussian) hbounded
  filter_upwards [hendpoint, hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant]
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
      ((partialSum_measurable (block n)).div_const (scale n))
      measurableSet_Icc]
    unfold independentIncrementLaw
    apply measure_mono
    intro increment hstay
    have hclosed := (staysIn_Icc_iff_inClosedInterval
      (lower * scale n) (upper * scale n) (block n) (x : ℝ)
      x.property increment).mp hstay
    have hendpoint : (x : ℝ) + partialSum (block n) increment ∈
        Set.Icc (lower * scale n) (upper * scale n) := by
      have hlast := hclosed ⟨block n, Nat.lt_succ_self (block n)⟩
      simpa [InClosedInterval, InWindows, history] using hlast
    let normalizedStart : ℝ := (x : ℝ) / scale n
    have hnormalizedStart : normalizedStart ∈ Set.Icc lower upper := by
      constructor
      · apply (le_div_iff₀ hnScale).2
        simpa [normalizedStart, mul_comm] using x.property.1
      · apply (div_le_iff₀ hnScale).2
        simpa [normalizedStart, mul_comm] using x.property.2
    have hsumLower : lower - normalizedStart ≤
        partialSum (block n) increment / scale n := by
      have h := div_le_div_of_nonneg_right hendpoint.1 hnScale.le
      have h' : lower ≤ normalizedStart +
          partialSum (block n) increment / scale n := by
        calc
          lower = (lower * scale n) / scale n := by
            field_simp [hnScale.ne']
          _ ≤ ((x : ℝ) + partialSum (block n) increment) / scale n := h
          _ = normalizedStart + partialSum (block n) increment / scale n := by
            simp [normalizedStart, add_div]
      linarith
    have hsumUpper : partialSum (block n) increment / scale n ≤
        upper - normalizedStart := by
      have h := div_le_div_of_nonneg_right hendpoint.2 hnScale.le
      have h' : normalizedStart +
          partialSum (block n) increment / scale n ≤ upper := by
        calc
          normalizedStart + partialSum (block n) increment / scale n =
              ((x : ℝ) + partialSum (block n) increment) / scale n := by
            simp [normalizedStart, add_div]
          _ ≤ (upper * scale n) / scale n := h
          _ = upper := by field_simp [hnScale.ne']
      linarith
    have hsum : partialSum (block n) increment / scale n ∈
        Set.Icc (-(upper - lower)) (upper - lower) := by
      constructor
      · calc
          -(upper - lower) ≤ lower - normalizedStart := by
            have := hnormalizedStart.2
            linarith
          _ ≤ partialSum (block n) increment / scale n := hsumLower
      · calc
          partialSum (block n) increment / scale n ≤ upper - normalizedStart :=
            hsumUpper
          _ ≤ upper - lower := by
            have := hnormalizedStart.1
            linarith
    exact hsum
  exact hsub.trans (le_of_lt hnEndpoint)

/-- The endpoint-CLT row bound controls survival over every number of steps.
The exponent is the number of complete diffusive blocks; an incomplete final
block is discarded by the sub-Markov comparison. -/
theorem eventually_horizontalTubeProbability_le_pow_diffusiveBlockCount
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {a constant q : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hconstant : 0 < constant) (hq : 0 < q) (hqOne : q < 1)
    (hgaussian : (gaussianReal 0 1).map
        (fun z : ℝ => z * Real.sqrt constant)
        (Set.Icc (-1 : ℝ) 1) < ENNReal.ofReal q) :
    ∀ᶠ n : ℕ in atTop,
      horizontalTubeProbability (independentIncrementLaw ν) a (scale n) n ≤
        ENNReal.ofReal q ^ (n / diffusiveBlockLength constant scale n) := by
  have hrow := eventually_uniform_killedBlock_remainingMass_le_of_endpointCLT
    ν hcentered hsecondMoment hscale (-a) (1 - a) constant q (by linarith)
    hconstant hq hqOne (by simpa using hgaussian)
  filter_upwards [hrow, hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant]
    with n hnRow hnScale hnBlock
  have hnRow' : ∀ x : Set.Icc ((-a) * scale n) ((1 - a) * scale n),
      Kernel.remainingMass
          (killedIncrementKernelOn ν
            (Set.Icc ((-a) * scale n) ((1 - a) * scale n)) measurableSet_Icc)
          (diffusiveBlockLength constant scale n) x ≤ ENNReal.ofReal q := by
    simpa only using hnRow
  have hbound := Kernel.remainingMass_le_pow_div
    (killedIncrementKernelOn ν
      (Set.Icc ((-a) * scale n) ((1 - a) * scale n)) measurableSet_Icc)
    (diffusiveBlockLength constant scale n) n
    ⟨0, by constructor <;> nlinarith⟩ (ENNReal.ofReal q) hnRow'
  rw [← remainingMass_killedIncrementKernelOn_Icc_eq_horizontalTubeProbability
    ν a (scale n) ha0.le ha1.le hnScale.le n]
  simpa [neg_mul] using hbound

end ProbabilityTheory.RandomWalk
