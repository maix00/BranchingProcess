/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Target.ExtremalPair

/-!
# Target mass lower bounds

The public declarations in this module are:

All names below are declarations in
`ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval`.

Write $N=\texttt{interiorCount}$, $K_N=\texttt{intervalKernel}(N)$,
$q_N=\cos(\pi/(N+1))$, $\phi_0(x)=\texttt{intervalSineWeight}(N,x)$,
and $T$ for the finite terminal target. The constants $a,b,p$ bound the
starting weight, target weights on reachable sites, and target density.

- `targetMass_ge_groundStateDensity_bound` gives a lower bound on target
  mass:
  $4abp q_N^n-4q_N^{2n}/(1-q_N^n)\le\sum_{y\in T}K_N^n(x,y)$,
  assuming ground-state lower bounds $a,b$ at the start and
  parity-compatible endpoints and target density at least $p$.
- `half_principalScale_le_targetMass` absorbs this geometric error when
  $q_N^n\le(4abp)/(4abp+8)$, yielding
  $2abp q_N^n\le\sum_{y\in T}K_N^n(x,y)$.

The paired principal modes give a useful lower bound whenever a terminal
target contains a positive proportion of parity-reachable sites in the
interior, where the ground state is bounded below.
-/

open scoped BigOperators Matrix

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

/-- If the principal-mode scale `r` is small compared with its coefficient,
the geometric remainder costs at most half the principal term. -/
private lemma half_mul_mul_le_mul_sub_geometricError
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

end ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval
