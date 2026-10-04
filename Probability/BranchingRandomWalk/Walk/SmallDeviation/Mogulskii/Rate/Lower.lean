/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.BlockScale
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Return.Uniform
public import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Blocking
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Mogulskii lower rate from uniform return blocks

This file converts a positive uniform return-block estimate into a normalized
real logarithmic `liminf` bound.  The probabilistic construction and the
integer block asymptotics remain separate inputs.
-/

open Filter MeasureTheory Set Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A positive uniform return-block bound gives the expected normalized
logarithmic lower rate for the ambient killed walk, from every fixed
normalized initial point in the return interval. -/
theorem mul_log_toReal_le_liminf_normalizedLog_remainingMass_of_return
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {outerLower outerUpper returnLower returnUpper initial : ℝ}
    (hinitial : initial ∈ Set.Icc returnLower returnUpper)
    (lowerBound : ENNReal) (hlowerBound : 0 < lowerBound)
    (hlowerBoundOne : lowerBound ≤ 1)
    (hblock : ∀ᶠ n in atTop,
      ∀ x : Set.Icc returnLower returnUpper,
        lowerBound ≤ returnKernel ν
          (Set.Icc (scale n * outerLower) (scale n * outerUpper)) measurableSet_Icc
          (Set.Icc (scale n * returnLower) (scale n * returnUpper)) measurableSet_Icc
          (blocks * diffusiveBlockLength constant scale n)
          ⟨scale n * x, by
            constructor <;> nlinarith [x.property.1, x.property.2,
              hscalePos n]⟩ univ) :
    (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
      atTop.liminf (fun n =>
        scale n ^ 2 / (n : ℝ) *
          Real.log (Kernel.remainingMass
            (killedIncrementKernel ν
              (Set.Icc (scale n * outerLower) (scale n * outerUpper))
              measurableSet_Icc) n
            (scale n * initial)).toReal) := by
  let length : ℕ → ℕ := fun n =>
    blocks * diffusiveBlockLength constant scale n
  let exponent : ℕ → ℕ := fun n => n / length n + 1
  let coefficient : ℕ → ℝ := fun n =>
    (exponent n : ℝ) * scale n ^ 2 / (n : ℝ)
  let probability : ℕ → ENNReal := fun n => Kernel.remainingMass
    (killedIncrementKernel ν
      (Set.Icc (scale n * outerLower) (scale n * outerUpper)) measurableSet_Icc)
    n (scale n * initial)
  have hlength : ∀ᶠ n in atTop, 0 < length n := by
    filter_upwards [hscale.eventually_diffusiveBlockLength_pos hconstant]
      with n hn
    exact Nat.mul_pos hblocks hn
  have hprobability : ∀ᶠ n in atTop,
      lowerBound ^ exponent n ≤ probability n := by
    have h :=
      eventually_pow_succ_div_le_remainingMass_killedIncrementKernel_Icc
        ν outerLower outerUpper returnLower returnUpper scale length id
        lowerBound hscalePos hlength hblock
    filter_upwards [h] with n hn
    simpa only [probability, exponent, id_eq] using hn
      (⟨scale n * initial, by
        constructor <;> nlinarith [hinitial.1, hinitial.2,
          hscalePos n]⟩ :
        Set.Icc (scale n * returnLower) (scale n * returnUpper))
  have hlowerBoundTop : lowerBound ≠ ⊤ :=
    ne_of_lt (hlowerBoundOne.trans_lt ENNReal.one_lt_top)
  have hlowerBoundReal : 0 < lowerBound.toReal :=
    ENNReal.toReal_pos hlowerBound.ne' hlowerBoundTop
  have hlog : ∀ᶠ n in atTop,
      coefficient n * Real.log lowerBound.toReal ≤
        scale n ^ 2 / (n : ℝ) * Real.log (probability n).toReal := by
    filter_upwards [hprobability, eventually_gt_atTop 0]
      with n hn hnPos
    have hprobabilityOne : probability n ≤ 1 := by
      exact Kernel.remainingMass_le_one
        (killedIncrementKernel ν
          (Set.Icc (scale n * outerLower) (scale n * outerUpper))
          measurableSet_Icc) n _
    have hprobabilityTop : probability n ≠ ⊤ :=
      ne_of_lt (hprobabilityOne.trans_lt ENNReal.one_lt_top)
    have hpowTop : lowerBound ^ exponent n ≠ ⊤ := by
      exact ENNReal.pow_ne_top hlowerBoundTop
    have hreal : (lowerBound ^ exponent n).toReal ≤
        (probability n).toReal :=
      (ENNReal.toReal_le_toReal hpowTop hprobabilityTop).2 hn
    have hlogReal := Real.log_le_log
      (by simpa [ENNReal.toReal_pow] using
        pow_pos hlowerBoundReal (exponent n)) hreal
    rw [ENNReal.toReal_pow, Real.log_pow] at hlogReal
    have hratioNonneg : 0 ≤ scale n ^ 2 / (n : ℝ) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hlogReal hratioNonneg
    calc
      coefficient n * Real.log lowerBound.toReal =
          scale n ^ 2 / (n : ℝ) *
            ((exponent n : ℝ) * Real.log lowerBound.toReal) := by
        dsimp [coefficient]
        ring
      _ ≤ _ := hmul
  have hcoefficient : Tendsto coefficient atTop
      (nhds (1 / ((blocks : ℝ) * constant))) := by
    simpa [coefficient, exponent, length] using
      hscale.tendsto_succ_completeReturnBlockCount_mul_sq_div
        hconstant hblocks
  have hleft : Tendsto
      (fun n => coefficient n * Real.log lowerBound.toReal) atTop
      (nhds ((1 / ((blocks : ℝ) * constant)) *
        Real.log lowerBound.toReal)) :=
    hcoefficient.mul_const _
  have hrightUpper : ∀ᶠ n in atTop,
      scale n ^ 2 / (n : ℝ) * Real.log (probability n).toReal ≤ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hprobabilityOne : probability n ≤ 1 := by
      exact Kernel.remainingMass_le_one
        (killedIncrementKernel ν
          (Set.Icc (scale n * outerLower) (scale n * outerUpper))
          measurableSet_Icc) n _
    have htoRealOne : (probability n).toReal ≤ 1 := by
      exact (ENNReal.toReal_le_toReal
        (ne_of_lt (hprobabilityOne.trans_lt ENNReal.one_lt_top))
        ENNReal.one_ne_top).2 hprobabilityOne
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Real.log_nonpos ENNReal.toReal_nonneg htoRealOne)
  calc
    (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal =
        atTop.liminf
          (fun n => coefficient n * Real.log lowerBound.toReal) :=
      hleft.liminf_eq.symm
    _ ≤ atTop.liminf (fun n =>
        scale n ^ 2 / (n : ℝ) * Real.log (probability n).toReal) :=
      Filter.liminf_le_liminf hlog hleft.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hrightUpper)
    _ = _ := rfl

/-- The preceding return-block argument stated as the horizontal-tube event.
The starting point is zero, so the normalized return interval must contain
zero.  This covers the interior horizontal-tube lower bound; boundary tubes
require a separate entrance estimate. -/
theorem mul_log_toReal_le_liminf_normalizedLog_horizontalTubeProbability_of_return
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hscalePos : ∀ n, 0 < scale n)
    {constant : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    {a returnLower returnUpper : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hreturnZero : (0 : ℝ) ∈ Set.Icc returnLower returnUpper)
    (lowerBound : ENNReal) (hlowerBound : 0 < lowerBound)
    (hlowerBoundOne : lowerBound ≤ 1)
    (hblock : ∀ᶠ n in atTop,
      ∀ x : Set.Icc returnLower returnUpper,
        lowerBound ≤ returnKernel ν
          (Set.Icc (scale n * (-a)) (scale n * (1 - a))) measurableSet_Icc
          (Set.Icc (scale n * returnLower) (scale n * returnUpper)) measurableSet_Icc
          (blocks * diffusiveBlockLength constant scale n)
          ⟨scale n * x, by
            constructor <;> nlinarith [x.property.1, x.property.2,
              hscalePos n, ha0, ha1]⟩ univ) :
    (1 / ((blocks : ℝ) * constant)) * Real.log lowerBound.toReal ≤
      atTop.liminf (fun n =>
        scale n ^ 2 / (n : ℝ) *
          Real.log (horizontalTubeProbability
            (independentIncrementLaw ν) a (scale n) n).toReal) := by
  have hkernel :=
    mul_log_toReal_le_liminf_normalizedLog_remainingMass_of_return
      ν hscale hscalePos hconstant hblocks hreturnZero lowerBound
      hlowerBound hlowerBoundOne hblock
  convert hkernel using 1
  apply congrArg (fun f => atTop.liminf f)
  funext n
  congr 1
  simp only [mul_zero]
  have hmass : Kernel.remainingMass
      (killedIncrementKernel ν
        (Set.Icc (scale n * (-a)) (scale n * (1 - a))) measurableSet_Icc)
      n 0 = horizontalTubeProbability
        (independentIncrementLaw ν) a (scale n) n := by
    exact
      remainingMass_killedIncrementKernel_scaled_Icc_eq_horizontalTubeProbability
        ν a (scale n) n
  rw [hmass]

end ProbabilityTheory.RandomWalk
