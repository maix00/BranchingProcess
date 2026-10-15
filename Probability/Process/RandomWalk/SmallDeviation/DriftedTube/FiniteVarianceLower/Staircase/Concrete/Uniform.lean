/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Concrete.ConditionalLower
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Concrete.ConditionalUpper
public import Analysis.Asymptotics.SequentialEventually

/-!
# Uniform tilted-tube bounds with fixed geometric margins

The public theorem in this file is:

- `exists_uniform_concreteStaircase_bounds_of_powerBlock`: for fixed
  interior-window fractions, margins, and rate parameters, a single
  threshold in the real tube width controls both endpoint events for every
  admissible starting boundary and every horizon
  $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$.

This is the passage from the sequential estimates to the common threshold
used in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-! The integer bin count is chosen before the fixed windows and rate margins. -/
private theorem exists_staircase_bin_count
    {sigma d v : ℝ}
    (hrate : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    (hv : 0 < v) :
    ∃ m : ℕ, 2 ≤ m ∧
      (Real.pi ^ 2 / 2) * sigma ^ 2 < d * staircaseBinWidth m ^ 2 ∧
      1 / (3 * (m : ℝ)) < v := by
  have hdenom : Tendsto (fun m : ℕ => 3 * (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  have hinv : Tendsto (fun m : ℕ => 1 / (3 * (m : ℝ))) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hdenom using 1
    funext m
    simp [one_div, mul_inv_rev, mul_comm]
  have hbeta : Tendsto staircaseBinWidth atTop (𝓝 (1 : ℝ)) := by
    convert (tendsto_const_nhds.sub hinv : Tendsto
      (fun m : ℕ => 1 - 1 / (3 * (m : ℝ))) atTop (𝓝 (1 - 0))) using 1
    · funext m
      unfold staircaseBinWidth
      simp [one_div, mul_inv_rev, mul_comm]
    · norm_num
  have hrateLimit : Tendsto (fun m : ℕ => d * staircaseBinWidth m ^ 2)
      atTop (𝓝 d) := by
    convert tendsto_const_nhds.mul (hbeta.pow 2) using 1
    norm_num
  have hmRate : ∀ᶠ m : ℕ in atTop,
      (Real.pi ^ 2 / 2) * sigma ^ 2 < d * staircaseBinWidth m ^ 2 :=
    hrateLimit.eventually (eventually_gt_nhds hrate)
  have hmV : ∀ᶠ m : ℕ in atTop, 1 / (3 * (m : ℝ)) < v :=
    hinv.eventually (eventually_lt_nhds hv)
  obtain ⟨m, hm⟩ := (Filter.eventually_ge_atTop 2 |>.and hmRate |>.and hmV).exists
  exact ⟨m, hm.1.1, hm.1.2, hm.2⟩


private theorem exists_staircase_rate_margins
    {sigma d : ℝ} {m : ℕ} (hm : 2 ≤ m)
    (hrate : (Real.pi ^ 2 / 2) * sigma ^ 2 <
      d * staircaseBinWidth m ^ 2) :
    ∃ blockRate narrowedRate : ℝ,
      0 ≤ blockRate ∧ 0 < d - blockRate ∧
      (Real.pi ^ 2 / 2) * sigma ^ 2 < narrowedRate ∧
      narrowedRate < blockRate * staircaseBinWidth m ^ 2 := by
  let K : ℝ := (Real.pi ^ 2 / 2) * sigma ^ 2
  let beta : ℝ := staircaseBinWidth m
  have hbeta : 0 < beta := staircaseBinWidth_pos hm
  have hbetaSq : 0 < beta ^ 2 := sq_pos_of_pos hbeta
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdiv : K / beta ^ 2 < d :=
    (div_lt_iff₀ hbetaSq).2 hrate
  have hd : 0 < d := by
    have hquot : 0 ≤ K / beta ^ 2 := div_nonneg hK hbetaSq.le
    linarith
  let blockRate : ℝ := (K / beta ^ 2 + d) / 2
  have hblockNonneg : 0 ≤ blockRate := by dsimp [blockRate]; positivity
  have hblockLt : blockRate < d := by dsimp [blockRate]; linarith
  have hKBlock : K < blockRate * beta ^ 2 := by
    have hmid : K / beta ^ 2 < blockRate := by
      dsimp [blockRate]; linarith
    have hmul := mul_lt_mul_of_pos_right hmid hbetaSq
    have heq : K / beta ^ 2 * beta ^ 2 = K := by field_simp
    rw [heq] at hmul
    exact hmul
  let narrowedRate : ℝ := (K + blockRate * beta ^ 2) / 2
  refine ⟨blockRate, narrowedRate, hblockNonneg, ?_, ?_, ?_⟩
  · linarith
  · change K < narrowedRate
    dsimp [narrowedRate]
    linarith
  · change narrowedRate < blockRate * beta ^ 2
    dsimp [narrowedRate]
    linarith


/-- The paper's common large-width threshold for both endpoint events,
once its fixed bin fractions and strict margins have been chosen. -/
theorem exists_uniform_concreteStaircase_bounds_of_powerBlock
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma narrowedRate uInterior vInterior
      uLower vLower uUpper vUpper : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (m : ℕ) (hm : 2 ≤ m)
    (huInterior : 0 < uInterior)
    (huvInterior : uInterior < vInterior)
    (hvInterior : vInterior < 1)
    (huLower : 0 < uLower)
    (huvLower : uLower < vLower)
    (hvLower : vLower < 1)
    (huUpper : 0 < uUpper)
    (huvUpper : uUpper < vUpper)
    (hvUpper : vUpper < 1)
    (hrateMogulskii : (Real.pi ^ 2 / 2) * sigma ^ 2 < narrowedRate)
    {margin drift endpointFraction blockRate totalRate alpha epsilon eta : ℝ}
    (heta : 0 < eta) (hetaOne : eta < 1) (hetaEpsilon : eta < epsilon)
    (hmargin : 0 < margin) (hdrift : 0 ≤ drift)
    (hendpoint : 0 ≤ endpointFraction)
    (hblockRate : 0 ≤ blockRate)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hdelta : 0 < totalRate - blockRate)
    (hrate : narrowedRate < blockRate * staircaseBinWidth m ^ 2)
    (hinteriorLower : (1 / 3 : ℝ) / staircaseBinWidth m +
      margin < uInterior)
    (hinteriorUpper : vInterior + margin ≤
      ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hlowerLower : margin ≤ uLower)
    (hlowerUpper : vLower + margin ≤
      (endpointFraction - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hupperLower : max (1 - endpointFraction) 0 /
        staircaseBinWidth m + margin < uUpper)
    (hupperUpper : vUpper + margin ≤
      (1 - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m) :
    ∃ threshold : ℝ, ∀ width ≥ threshold, ∀ horizon : ℕ, ∀ base : ℝ,
      Nat.floor (width ^ (2 + epsilon)) ≤ horizon →
      -base ∈ Set.Icc 0 width →
      Real.exp (-totalRate * (horizon : ℝ) / width ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeEndpointWindowEvent horizon width
            drift base endpointFraction) ∧
      Real.exp (-totalRate * (horizon : ℝ) / width ^ 2) ≤
        (iidSequenceLaw ν).real
          (driftedTubeUpperEndpointWindowEvent horizon width
            drift base endpointFraction) := by
  let admissible : ℝ → ℕ × ℝ → Prop := fun width parameter =>
    Nat.floor (width ^ (2 + epsilon)) ≤ parameter.1 ∧
      -parameter.2 ∈ Set.Icc 0 width
  let bound : ℝ → ℕ × ℝ → Prop := fun width parameter =>
    Real.exp (-totalRate * (parameter.1 : ℝ) / width ^ 2) ≤
      (iidSequenceLaw ν).real
        (driftedTubeEndpointWindowEvent parameter.1 width
          drift parameter.2 endpointFraction) ∧
    Real.exp (-totalRate * (parameter.1 : ℝ) / width ^ 2) ≤
      (iidSequenceLaw ν).real
        (driftedTubeUpperEndpointWindowEvent parameter.1 width
          drift parameter.2 endpointFraction)
  have hseq (width : ℕ → ℝ) (parameter : ℕ → ℕ × ℝ)
      (hwidth : Tendsto width atTop atTop)
      (hadmissible : ∀ n, admissible (width n) (parameter n)) :
      ∀ᶠ n : ℕ in atTop, bound (width n) (parameter n) := by
    let horizon : ℕ → ℕ := fun n => (parameter n).1
    let base : ℕ → ℝ := fun n => (parameter n).2
    have hhorizon : ∀ᶠ n : ℕ in atTop,
        Nat.floor (width n ^ (2 + epsilon)) ≤ horizon n :=
      Filter.Eventually.of_forall (fun n => (hadmissible n).1)
    have hstart : ∀ᶠ n : ℕ in atTop,
        -base n ∈ Set.Icc 0 (width n) :=
      Filter.Eventually.of_forall (fun n => (hadmissible n).2)
    have hlower :=
      eventually_concreteStaircaseLowerBound_of_powerBlock
        hν hsigma hrho hrhoSmall m hm huInterior huvInterior hvInterior
        huLower huvLower hvLower hrateMogulskii hwidth hhorizon
        heta hetaOne hetaEpsilon hmargin hdrift hstart
        hendpoint hblockRate halpha hepsilon hdelta hrate
        hinteriorLower hinteriorUpper hlowerLower hlowerUpper
    have hupper :=
      eventually_concreteStaircaseUpperEndpointLowerBound_of_powerBlock
        hν hsigma hrho hrhoSmall m hm huInterior huvInterior hvInterior
        huUpper huvUpper hvUpper hrateMogulskii hwidth hhorizon
        heta hetaOne hetaEpsilon hmargin hdrift hstart
        hendpoint hblockRate halpha hepsilon hdelta hrate
        hinteriorLower hinteriorUpper hupperLower hupperUpper
    filter_upwards [hlower, hupper] with n hnLower hnUpper
    exact ⟨hnLower, hnUpper⟩
  obtain ⟨threshold, hthreshold⟩ :=
    Asymptotics.eventually_uniform_atTop_of_forall_tendsto_nat
      admissible bound hseq
  refine ⟨threshold, ?_⟩
  intro width hwidth horizon base hhorizon hstart
  exact hthreshold width hwidth (horizon, base) ⟨hhorizon, hstart⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
