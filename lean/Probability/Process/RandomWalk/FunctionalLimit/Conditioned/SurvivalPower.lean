/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival
public import Probability.Process.RandomWalk.Fluctuation.StableLadderTimeTail
public import Analysis.Asymptotics.RegularVariation.LowerPower
public import Analysis.Asymptotics.ShiftedFloor

/-!
# Survival power bounds from regular variation

The public objects and theorems in this file are:

- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbabilityReal:
  $x\mapsto\mathbb P(C_{\lfloor x\rfloor})$.
- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbabilityReal_eq_firstDescendingLadderTime_tail:
  $\mathbb P(C_{\lfloor x\rfloor})=\mathbb P(T^-_1>\lfloor x\rfloor)$.
- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbabilityReal_regularVariation_of_ladderTimeTail:
  regular variation of the first descending ladder-time tail transfers
  to the survival probability.
- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbabilityReal_regularVariation_of_ladderTimeStableAttraction:
  stable attraction of the finite first ladder time at index $1/2$
  gives regular variation of $\mathbb P(C_{\lfloor x\rfloor})$ at index $-1/2$.
- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbabilityReal_antitone:
  $x\le y$ implies $\mathbb P(C_{\lfloor y\rfloor})\le
  \mathbb P(C_{\lfloor x\rfloor})$.
- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalProbabilityReal_pos:
  for centered increments with positive variance,
  $\mathbb P(C_{\lfloor x\rfloor})>0$.
- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_survivalProbabilityReal_ge_power:
  if $x\mapsto\mathbb P(C_{\lfloor x\rfloor})$ is regularly varying with
  index $-1/2$, then for every $\alpha>0$ it eventually exceeds
  $C/x^{(1+\alpha)/2}$ for some $C>0$.
- ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveSurvivalProbability_ge_power:
  at $N_n=\lfloor\Delta_n^2\rfloor-m$ with $\Delta_n\to\infty$,
  $\mathbb P(C_{N_n})\ge C\Delta_n^{-1-\alpha}$ eventually.

The regular-variation input is the finite-variance specialization of
Caravenna and Chaumont, *Invariance principles for random walks conditioned
to stay positive*, Lemma 2.1 (DOI 10.1214/07-AIHP119). The power bound is
the Potter step in Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Appendix A.2, first lemma.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- Survival probability at a real time parameter, rounded down to the
finite discrete horizon. -/
noncomputable def survivalProbabilityReal (ν : Measure ℝ)
    (x : ℝ) : ℝ :=
  ((iidSequenceLaw ν)
    {increment | SurvivesNonnegative (Nat.floor x) increment}).toReal

/-- The real-indexed survival probability is the tail of the first strict
descending ladder time. This is the identity $C_N=\{T^-_1>N\}$ used before
equation (2.3) in Caravenna--Chaumont, *Invariance principles for random
walks conditioned to stay positive*, Lemma 2.1. -/
theorem survivalProbabilityReal_eq_firstDescendingLadderTime_tail
    (ν : Measure ℝ) (x : ℝ) :
    survivalProbabilityReal ν x =
      firstDescendingLadderTimeTailReal (iidSequenceLaw ν) x := by
  unfold survivalProbabilityReal
    firstDescendingLadderTimeTailReal
  rw [measure_survival_eq_firstDescendingLadderTime_gt]

/-- Caravenna--Chaumont, Lemma 2.1, passes from the first strict
descending ladder-time tail to the survival probability using
$C_N=\{T^-_1>N\}$. The fluctuation-theory step establishing the tail's
regular variation is separate from this identification. -/
theorem survivalProbabilityReal_regularVariation_of_ladderTimeTail
    (ν : Measure ℝ)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (firstDescendingLadderTimeTailReal (iidSequenceLaw ν))
      (-(1 / 2 : ℝ))) :
    Asymptotics.IsRegularlyVaryingAtTop
      (survivalProbabilityReal ν) (-(1 / 2 : ℝ)) := by
  simpa only [funext (survivalProbabilityReal_eq_firstDescendingLadderTime_tail ν)]
    using htail

/-- The stable-ladder-time and one-sided-tail steps in
Caravenna--Chaumont, *Invariance principles for random walks conditioned
to stay positive*, Lemma 2.1, yield its finite-variance survival exponent
through $C_N=\{T^-_1>N\}$. -/
theorem survivalProbabilityReal_regularVariation_of_ladderTimeStableAttraction
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hfinite : iidSequenceLaw ν {increment |
      strictDescendingLadderTime increment 1 = ⊤} = 0)
    {limit : Measure ℝ}
    (hlimit : IsAlphaStable (1 / 2 : ℝ) limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong
      (firstDescendingLadderTimeLaw (iidSequenceLaw ν)) limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    Asymptotics.IsRegularlyVaryingAtTop
      (survivalProbabilityReal ν) (-(1 / 2 : ℝ)) := by
  have htail :=
    firstDescendingLadderTimeTailReal_regularVariation_of_stableAttraction
      hfinite hlimit h (by norm_num) (by norm_num)
  exact survivalProbabilityReal_regularVariation_of_ladderTimeTail ν htail

/-- Longer survival has smaller probability. -/
theorem survivalProbabilityReal_antitone
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Antitone (survivalProbabilityReal ν) := by
  intro x y hxy
  unfold survivalProbabilityReal
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (survivalProbability_antitone ν (Nat.floor_le_floor hxy))

/-- Centered nondegenerate increments give a positive finite-time
survival probability at every real-indexed horizon. -/
theorem survivalProbabilityReal_pos
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (x : ℝ) :
    0 < survivalProbabilityReal ν x := by
  unfold survivalProbabilityReal
  exact ENNReal.toReal_pos
    (ne_of_gt (survivalProbability_pos_of_positiveIncrement ν
      (hν.measure_Ioi_zero_pos hsigma) (Nat.floor x)))
    (measure_ne_top _ _)

/-- The Potter lower bound for the survival probability in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, first lemma. Its regular-variation input is precisely the
conclusion of Caravenna--Chaumont, Lemma 2.1, specialized to finite
variance; establishing that input from the increment law is a separate
fluctuation-theory result. -/
theorem exists_eventually_survivalProbabilityReal_ge_power
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hreg : Asymptotics.IsRegularlyVaryingAtTop
      (survivalProbabilityReal ν) (-(1 / 2 : ℝ)))
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      C / x ^ ((1 + alpha) / 2) ≤ survivalProbabilityReal ν x := by
  have hmono : Asymptotics.IsEventuallyMonotoneAtTop
      (fun x => (survivalProbabilityReal ν x)⁻¹) := by
    refine ⟨0, ?_⟩
    intro x y _ hxy
    exact (inv_le_inv₀
      (survivalProbabilityReal_pos ν hν hsigma x)
      (survivalProbabilityReal_pos ν hν hsigma y)).2
        (survivalProbabilityReal_antitone ν hxy)
  have hpower := hreg.exists_eventually_lower_power_of_inverse_monotone
    (ε := alpha / 2) hmono
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (div_pos halpha (by norm_num))
  have hexponent : (1 / 2 : ℝ) + alpha / 2 = (1 + alpha) / 2 := by ring
  simpa only [hexponent] using hpower

/-- Potter's bound at the exact horizon
$N_n=\lfloor\Delta_n^2\rfloor-m$ in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, first lemma. The regular variation is the conclusion of
Caravenna--Chaumont, Lemma 2.1 (DOI 10.1214/07-AIHP119). -/
theorem exists_eventually_diffusiveSurvivalProbability_ge_power
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (hreg : Asymptotics.IsRegularlyVaryingAtTop
      (survivalProbabilityReal ν) (-(1 / 2 : ℝ)))
    {alpha : ℝ} (halpha : 0 < alpha)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        ((iidSequenceLaw ν)
          {increment | SurvivesNonnegative
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n -
              offset) increment}).toReal := by
  obtain ⟨C, hC, hpower⟩ :=
    exists_eventually_survivalProbabilityReal_ge_power ν hν hsigma
      hreg halpha
  let argument : ℕ → ℝ := fun n => width n ^ 2
  let horizon : ℕ → ℕ :=
    fun n => Asymptotics.floorBlockLength argument n - offset
  have hargument : Tendsto argument atTop atTop := by
    have hmul : Tendsto (fun n => width n * width n) atTop atTop :=
      hwidth.atTop_mul_atTop₀ hwidth
    simpa [argument, pow_two] using hmul
  have hhorizon : Tendsto horizon atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    have hfloor :=
      (Asymptotics.tendsto_floorBlockLength_atTop hargument).eventually
        (eventually_ge_atTop (bound + offset))
    filter_upwards [hfloor] with n hn
    dsimp [horizon]
    omega
  have hhorizonReal : Tendsto (fun n => (horizon n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hhorizon
  have hpowerAtHorizon := hhorizonReal.eventually hpower
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hhorizonPos : ∀ᶠ n : ℕ in atTop, 0 < horizon n :=
    hhorizon.eventually (eventually_gt_atTop 0)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpowerAtHorizon, hwidthPos, hhorizonPos]
    with n hbound hwidthN hhorizonN
  have hwidthSq : (horizon n : ℝ) ≤ width n ^ 2 := by
    calc
      (horizon n : ℝ) ≤
          (Asymptotics.floorBlockLength argument n : ℝ) := by
        exact_mod_cast Nat.sub_le _ _
      _ ≤ argument n := by
        change (Nat.floor (argument n) : ℝ) ≤ argument n
        exact Nat.floor_le (sq_nonneg _)
      _ = width n ^ 2 := rfl
  have hp : 0 ≤ (1 + alpha) / 2 := by linarith
  have hpowLe :
      (horizon n : ℝ) ^ ((1 + alpha) / 2) ≤
        width n ^ (1 + alpha) := by
    calc
      (horizon n : ℝ) ^ ((1 + alpha) / 2) ≤
          (width n ^ 2) ^ ((1 + alpha) / 2) :=
        Real.rpow_le_rpow (by positivity) hwidthSq hp
      _ = width n ^ (1 + alpha) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hwidthN.le]
        congr 1
        ring
  have hhorpow : 0 < (horizon n : ℝ) ^ ((1 + alpha) / 2) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hhorizonN) _
  have hwidthpow : 0 < width n ^ (1 + alpha) :=
    Real.rpow_pos_of_pos hwidthN _
  have hdiv : C / width n ^ (1 + alpha) ≤
      C / (horizon n : ℝ) ^ ((1 + alpha) / 2) := by
    exact (div_le_div_iff₀ hwidthpow hhorpow).2
      (by nlinarith [mul_le_mul_of_nonneg_left hpowLe hC.le])
  have hsurvival :
      survivalProbabilityReal ν (horizon n : ℝ) =
        ((iidSequenceLaw ν)
          {increment | SurvivesNonnegative (horizon n) increment}).toReal := by
    simp [survivalProbabilityReal]
  rw [hsurvival] at hbound
  exact hdiv.trans hbound

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
