/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.ExtremalPair
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Diffusive.Lower

/-!
# Target mass lower bounds

The paired principal modes give a useful lower bound whenever a terminal
target contains a positive proportion of parity-reachable sites in the
interior, where the ground state is bounded below.
-/

open Filter Topology
open scoped BigOperators Matrix

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- If the principal-mode scale `r` is small compared with its coefficient,
the geometric remainder costs at most half the principal term. -/
theorem half_mul_mul_le_mul_sub_geometricError
    {coefficient r : ℝ} (hcoefficient : 0 ≤ coefficient)
    (hr : 0 < r) (hrOne : r < 1)
    (hsmall : r ≤ coefficient / (coefficient + 8)) :
    coefficient / 2 * r ≤
      coefficient * r - 4 * (r ^ 2 / (1 - r)) := by
  have hden : 0 < 1 - r := by linarith
  have hcoefDen : 0 < coefficient + 8 := by linarith
  have hsmall' : r * (coefficient + 8) ≤ coefficient :=
    (le_div_iff₀ hcoefDen).mp hsmall
  have hgap : 0 ≤ coefficient + 8 - r * (coefficient + 8) := by
    nlinarith [hsmall']
  have hdominates : 4 * r ^ 2 ≤ coefficient / 2 * r * (1 - r) := by
    nlinarith [mul_nonneg hr.le hgap]
  have herr : 4 * (r ^ 2 / (1 - r)) ≤ coefficient / 2 * r := by
    calc
      4 * (r ^ 2 / (1 - r)) = (4 * r ^ 2) / (1 - r) := by ring
      _ ≤ coefficient / 2 * r := (div_le_iff₀ hden).2 hdominates
  nlinarith [mul_nonneg hcoefficient hr.le]

/-- A pointwise lower bound on the ground state and a positive density of
parity-compatible target sites turn the extremal spectral pair into an
explicit target-mass lower bound.  The final term is the geometric bound on
all remaining modes. -/
theorem targetMass_ge_groundStateDensity_bound
    {interiorCount n : ℕ} (hcount : 1 < interiorCount) (hn : 0 < n)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount)
    {startWeight targetWeight proportion : ℝ}
    (htargetWeight : 0 ≤ targetWeight)
    (hproportion : 0 ≤ proportion)
    (hstart : startWeight ≤ intervalSineWeight interiorCount start)
    (htarget : ∀ finish ∈ intervalParityCompatibleTarget n start target,
      targetWeight ≤ intervalSineWeight interiorCount finish)
    (hcard : proportion * ((interiorCount + 1 : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget n start target).card) :
    4 * Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n *
        startWeight * targetWeight * proportion -
      4 * ((Real.cos
        (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^ 2 /
        (1 - Real.cos
          (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n)) ≤
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  let width : ℝ := ((interiorCount + 1 : ℕ) : ℝ)
  let compatible := intervalParityCompatibleTarget n start target
  let compatibleMass : ℝ := ∑ finish ∈ compatible,
    intervalSineWeight interiorCount finish
  have hq : 0 < q := by
    dsimp [q]
    exact intervalEigenvalue_pos hcount
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hcompatibleMass : targetWeight * compatible.card ≤ compatibleMass := by
    dsimp [compatibleMass]
    calc
      targetWeight * compatible.card = ∑ _finish ∈ compatible, targetWeight := by
        simp [mul_comm]
      _ ≤ ∑ finish ∈ compatible,
          intervalSineWeight interiorCount finish :=
        Finset.sum_le_sum fun finish hfinish => htarget finish hfinish
  have hcompatibleMass_nonneg : 0 ≤ compatibleMass := by
    dsimp [compatibleMass]
    exact Finset.sum_nonneg fun finish _ =>
      (intervalSineWeight_pos (Nat.zero_lt_of_lt hcount) finish).le
  have hdenseMass : targetWeight * (proportion * width) ≤ compatibleMass := by
    calc
      targetWeight * (proportion * width) ≤
          targetWeight * (compatible.card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard htargetWeight
      _ ≤ compatibleMass := hcompatibleMass
  have hstartMass : startWeight * (targetWeight * (proportion * width)) ≤
      intervalSineWeight interiorCount start * compatibleMass :=
    mul_le_mul hstart hdenseMass
      (mul_nonneg htargetWeight (mul_nonneg hproportion hwidth.le))
      (intervalSineWeight_pos (Nat.zero_lt_of_lt hcount) start).le
  have hpair := intervalKernel_extremalPair_eq_parityTargetMass
    hcount n target start
  have hpairLower :
      4 * q ^ n / width * startWeight *
          (targetWeight * (proportion * width)) ≤
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target)
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount) *
          intervalModeEigenvalue interiorCount
            ⟨0, Nat.zero_lt_of_lt hcount⟩ ^ n *
          intervalSineMode interiorCount
            ⟨0, Nat.zero_lt_of_lt hcount⟩ start +
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target)
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev *
          intervalModeEigenvalue interiorCount
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev ^ n *
          intervalSineMode interiorCount
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev start := by
    rw [hpair]
    dsimp [q, width, compatible, compatibleMass]
    have hbase : 0 ≤ 4 * Real.cos
        (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n /
        ((interiorCount + 1 : ℕ) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hstartMass hbase
    convert this using 1 <;> ring
  have hprincipal := intervalKernel_pow_targetMass_ge_extremalPair_sub_geometricError
    hcount hn target start
  dsimp [q, width] at hpairLower ⊢
  have hpairLower' :
      4 * Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n *
          startWeight * targetWeight * proportion ≤
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target)
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount) *
          intervalModeEigenvalue interiorCount
            ⟨0, Nat.zero_lt_of_lt hcount⟩ ^ n *
          intervalSineMode interiorCount
            ⟨0, Nat.zero_lt_of_lt hcount⟩ start +
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target)
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev *
          intervalModeEigenvalue interiorCount
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev ^ n *
          intervalSineMode interiorCount
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev start := by
    calc
      _ = 4 * Real.cos
          (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n /
            ((interiorCount + 1 : ℕ) : ℝ) * startWeight *
              (targetWeight * (proportion * ((interiorCount + 1 : ℕ) : ℝ))) := by
        field_simp [show ((interiorCount + 1 : ℕ) : ℝ) ≠ 0 by positivity]
      _ ≤ _ := hpairLower
  linarith

/-- A sufficiently small principal eigenvalue power turns the target-mass
estimate into a strictly positive core-to-core return bound. -/
theorem half_principalScale_le_targetMass
    {interiorCount n : ℕ} (hcount : 1 < interiorCount) (hn : 0 < n)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount)
    {startWeight targetWeight proportion : ℝ}
    (hstartWeight : 0 < startWeight)
    (htargetWeight : 0 < targetWeight) (hproportion : 0 < proportion)
    (hstart : startWeight ≤ intervalSineWeight interiorCount start)
    (htarget : ∀ finish ∈ intervalParityCompatibleTarget n start target,
      targetWeight ≤ intervalSineWeight interiorCount finish)
    (hcard : proportion * ((interiorCount + 1 : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget n start target).card)
    (hsmall : Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n ≤
      (4 * startWeight * targetWeight * proportion) /
        (4 * startWeight * targetWeight * proportion + 8)) :
    2 * startWeight * targetWeight * proportion *
        Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n ≤
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  let coefficient : ℝ :=
    4 * startWeight * targetWeight * proportion
  have hq : 0 < q := by
    dsimp [q]
    exact intervalEigenvalue_pos hcount
  have hqOne : q < 1 := by
    dsimp [q]
    exact intervalEigenvalue_lt_one (Nat.zero_lt_of_lt hcount)
  have hr : 0 < q ^ n := pow_pos hq _
  have hrOne : q ^ n < 1 := pow_lt_one₀ hq.le hqOne hn.ne'
  have hcoeff : 0 < coefficient := by
    dsimp [coefficient]
    positivity
  have hsmall' : q ^ n ≤ coefficient / (coefficient + 8) := by
    simpa [q, coefficient] using hsmall
  have hmass := targetMass_ge_groundStateDensity_bound hcount hn target start
    (startWeight := startWeight)
    (targetWeight := targetWeight) (proportion := proportion)
    htargetWeight.le hproportion.le hstart htarget hcard
  have hmass' : coefficient * q ^ n -
      4 * ((q ^ n) ^ 2 / (1 - q ^ n)) ≤
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish := by
    convert hmass using 1
    · dsimp [coefficient, q]
      ring_nf
  have hcombined := half_mul_mul_le_mul_sub_geometricError
    hcoeff.le hr hrOne hsmall'
  have hcombined' : coefficient / 2 * q ^ n ≤
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish :=
    hcombined.trans hmass'
  convert hcombined' using 1
  · dsimp [coefficient, q]
    ring_nf

/-- Uniform ground-state and parity-density bounds turn a diffusive block
into a uniform positive target-mass estimate.  The block parameter is chosen
large enough that the two-mode principal contribution dominates the
geometric spectral remainder. -/
theorem eventually_realBound_le_centeredDiffusiveTargetMass
    (radius time : ℕ → ℕ) (target : ∀ n, Finset (Fin (2 * radius n + 1)))
    (start : ∀ n, Fin (2 * radius n + 1))
    {startWeight targetWeight proportion c lowerBound : ℝ}
    (hradius : ∀ n, 0 < radius n) (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto
      (fun n => ((2 * (radius n + 1) : ℕ) : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2) atTop (nhds c))
    (hstartWeight : 0 < startWeight)
    (htargetWeight : 0 < targetWeight) (hproportion : 0 < proportion)
    (hstart : ∀ n, startWeight ≤
      intervalSineWeight (2 * radius n + 1) (start n))
    (htarget : ∀ n finish,
      finish ∈ intervalParityCompatibleTarget (time n) (start n) (target n) →
      targetWeight ≤ intervalSineWeight (2 * radius n + 1) finish)
    (hcard : ∀ n, proportion * ((2 * (radius n + 1) : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget (time n) (start n) (target n)).card)
    (hsmallLimit : Real.exp (c * (-(Real.pi ^ 2) / 2)) <
      (4 * startWeight * targetWeight * proportion) /
        (4 * startWeight * targetWeight * proportion + 8))
    (hlowerBound : lowerBound <
      (2 * startWeight * targetWeight * proportion) *
        Real.exp (c * (-(Real.pi ^ 2) / 2))) :
    ∀ᶠ n in atTop, lowerBound ≤
      ∑ finish ∈ target n,
        (intervalKernel (2 * radius n + 1) ^ time n) (start n) finish := by
  let width : ℕ → ℝ := fun n => ((2 * (radius n + 1) : ℕ) : ℝ)
  let qpow : ℕ → ℝ := fun n =>
    Real.cos (Real.pi / width n) ^ time n
  let coefficient : ℝ := 4 * startWeight * targetWeight * proportion
  have hpower : Tendsto qpow atTop
      (nhds (Real.exp (c * (-(Real.pi ^ 2) / 2)))) := by
    simpa [qpow, width] using
      tendsto_centeredPrincipalPower_of_diffusiveRatio
        radius time c hradius hwidth hratio
  have hcoefficient : 0 < coefficient := by
    dsimp [coefficient]
    positivity
  have hsmallEventually : ∀ᶠ n in atTop,
      qpow n ≤ coefficient / (coefficient + 8) := by
    have hthreshold :
        ∀ᶠ n in atTop, qpow n < coefficient / (coefficient + 8) :=
      hpower.eventually (eventually_lt_nhds (by simpa [coefficient] using hsmallLimit))
    exact hthreshold.mono fun _ h => h.le
  have hlowerEventually : ∀ᶠ n in atTop,
      lowerBound < coefficient / 2 * qpow n := by
    have hscaled : Tendsto (fun n => coefficient / 2 * qpow n)
        atTop (nhds (coefficient / 2 *
          Real.exp (c * (-(Real.pi ^ 2) / 2)))) :=
      (tendsto_const_nhds.mul hpower)
    have hstrict : lowerBound < coefficient / 2 *
        Real.exp (c * (-(Real.pi ^ 2) / 2)) := by
      dsimp [coefficient]
      nlinarith [hlowerBound]
    exact hscaled.eventually (eventually_gt_nhds hstrict)
  filter_upwards [hsmallEventually, hlowerEventually] with n hsmallN hlowerN
  have hwidthEq : width n =
      ((2 * radius n + 1 + 1 : ℕ) : ℝ) := by
    dsimp [width]
    push_cast
    ring
  have hcount : 1 < 2 * radius n + 1 := by
    have := hradius n
    omega
  have hcardN : proportion * ((2 * radius n + 1 + 1 : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget (time n) (start n) (target n)).card := by
    convert hcard n using 1
  have hsmallN' : Real.cos
        (Real.pi / ((2 * radius n + 1 + 1 : ℕ) : ℝ)) ^ time n ≤
      (4 * startWeight * targetWeight * proportion) /
        (4 * startWeight * targetWeight * proportion + 8) := by
    rw [← hwidthEq]
    simpa [qpow, width, coefficient] using hsmallN
  have hmass := half_principalScale_le_targetMass
    hcount
    (htime n) (target n) (start n)
    (startWeight := startWeight)
    (targetWeight := targetWeight) (proportion := proportion)
    hstartWeight htargetWeight hproportion (hstart n)
    (htarget n) hcardN hsmallN'
  have hmass' : 2 * startWeight * targetWeight * proportion * qpow n ≤
      ∑ finish ∈ target n,
        (intervalKernel (2 * radius n + 1) ^ time n) (start n) finish := by
    change 2 * startWeight * targetWeight * proportion *
        Real.cos (Real.pi / width n) ^ time n ≤ _
    rw [hwidthEq]
    exact hmass
  have hlowerN' : lowerBound ≤
      2 * startWeight * targetWeight * proportion * qpow n :=
    (le_of_lt hlowerN).trans_eq (by dsimp [coefficient]; ring)
  exact hlowerN'.trans hmass'

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
