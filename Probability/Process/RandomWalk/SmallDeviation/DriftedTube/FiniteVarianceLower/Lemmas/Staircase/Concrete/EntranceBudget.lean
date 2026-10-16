/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Power.PolynomialExponential
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.DiffusiveLower
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.PowerAssembly

/-!
# Lemma 3.5 entrance exponential budget

The supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_robustTransitionProbability_ge_exp_of_centeredFiniteVariance`:
  for $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$, the uniform entrance bound
  $C\Delta^{-2}$ from the private entrance estimate pays an exponential cost
  at most $\exp(-\delta L/\Delta^2)$.

This is the polynomial-to-exponential comparison used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.5. The general power-bound assembly remains in
`Entrance/Robust/PowerAssembly.lean`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The three entrance regimes yield the inverse-square bound for the
terminal window of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Appendix A.2, Lemma A.7. -/
private lemma exists_eventually_robustTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift : ℝ} (hdrift : 0 ≤ drift) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc 0 (width n),
        C / width n ^ 2 ≤
          (iidSequenceLaw ν
            (robustMovingTransitionEvent
              (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
              (width n) drift start)).toReal := by
  have hνneg : IsCenteredSecondMoment (ν.map fun x : ℝ => -x)
      (sigma ^ 2) := hν.map_neg
  have hplus (m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + (1 : ℝ)) ≤
        (iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
            (width n))).toReal := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two,
      FunctionalLimit.Conditioned.diffusiveTransitionHorizon] using
      (FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
        ν hν hsigma (by norm_num : (0 : ℝ) < 1 / 100)
        (by norm_num : (1 / 100 : ℝ) < 1 / 48) hwidth m)
  have hminus (m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + (1 : ℝ)) ≤
        (iidSequenceLaw (ν.map fun x : ℝ => -x)
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
            (width n))).toReal := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two,
      FunctionalLimit.Conditioned.diffusiveTransitionHorizon] using
      (FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
        (ν.map fun x : ℝ => -x) hνneg hsigma
        (by norm_num : (0 : ℝ) < 1 / 100)
        (by norm_num : (1 / 100 : ℝ) < 1 / 48) hwidth m)
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using
    (exists_eventually_robustTransitionProbability_ge_power_of_transitionBounds
      hν hsigma hwidth hdrift (by norm_num : (0 : ℝ) < 1)
      hplus hminus)

/-- The sequence estimate gives the same inverse-square constant for every
sufficiently large real width and every admissible starting point. -/
private lemma exists_uniform_robustTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {drift : ℝ} (hdrift : 0 ≤ drift) :
    ∃ C : ℝ, 0 < C ∧ ∃ threshold : ℝ, ∀ width ≥ threshold,
      ∀ start ∈ Set.Icc 0 width,
        C / width ^ 2 ≤
          (iidSequenceLaw ν
            (robustMovingTransitionEvent
              (Nat.floor (width ^ 2)) width drift start)).toReal := by
  classical
  by_contra hnot
  push Not at hnot
  have hbad (n : ℕ) : ∃ width : ℝ, (n + 1 : ℕ) ≤ width ∧
      ∃ start ∈ Set.Icc 0 width,
        (iidSequenceLaw ν
          (robustMovingTransitionEvent
            (Nat.floor (width ^ 2)) width drift start)).toReal <
              (1 / (n + 1 : ℕ) : ℝ) / width ^ 2 := by
    have hsmall : (0 : ℝ) < 1 / (n + 1 : ℕ) := by positivity
    obtain ⟨width, hwidth, start, hstart, hlt⟩ :=
      hnot (1 / (n + 1 : ℕ)) hsmall (n + 1 : ℕ)
    exact ⟨width, hwidth, start, hstart, hlt⟩
  choose width hwidth using hbad
  choose start hstart hlt using fun n => (hwidth n).2
  have hwidthLimit : Tendsto width atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    have hnat : ∀ᶠ n : ℕ in atTop, bound ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop bound)
    filter_upwards [hnat] with n hn
    have hstep : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.le_succ n)
    exact (hn.trans hstep).trans (hwidth n).1
  obtain ⟨C, hC, hprob⟩ :=
    exists_eventually_robustTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
      ν hν hsigma hwidthLimit hdrift
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 / (n + 1 : ℕ) : ℝ) < C := by
    have hlimit : Tendsto (fun n : ℕ => (1 / (n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact hlimit.eventually (eventually_lt_nhds hC)
  obtain ⟨n, hn⟩ := (hprob.and hsmall).exists
  have hwpos : 0 < width n := by
    have : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    exact this.trans_le (hwidth n).1
  have hden : 0 < width n ^ 2 := pow_pos hwpos _
  have hstrict : (1 / (n + 1 : ℕ) : ℝ) / width n ^ 2 < C / width n ^ 2 :=
    div_lt_div_of_pos_right hn.2 hden
  exact (lt_irrefl (C / width n ^ 2))
    ((lt_of_le_of_lt (hn.1 (start n) (hstart n)) (hlt n)).trans hstrict)


/-- The robust entrance cost is absorbed by the exponential budget after
the meander transition has been supplied for both the walk and its
reflection. -/
lemma exists_eventually_robustTransitionProbability_ge_exp_of_centeredFiniteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift delta epsilon : ℝ}
    (hdrift : 0 ≤ drift)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc 0 (width n), ∀ L : ℕ,
        Nat.floor (width n ^ (2 + epsilon)) ≤ L →
        Real.exp (-delta * (L : ℝ) / width n ^ 2) ≤
          (iidSequenceLaw ν).real
            (robustMovingTransitionEvent
              (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
              (width n) drift start) := by
  obtain ⟨C, hC, threshold, hpowerUniform⟩ :=
    exists_uniform_robustTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
      ν hν hsigma hdrift
  have hpower : ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc 0 (width n),
        C / width n ^ 2 ≤
          (iidSequenceLaw ν
            (robustMovingTransitionEvent
              (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
              (width n) drift start)).toReal := by
    filter_upwards [hwidth.eventually (eventually_ge_atTop threshold)] with n hn
    simpa only [Asymptotics.floorBlockLength] using hpowerUniform (width n) hn
  have hbudget := hwidth.eventually
    (Asymptotics.eventually_exp_neg_horizon_le_polynomial
      hC hdelta hepsilon (p := 2))
  filter_upwards [hpower, hbudget] with n hnPower hnBudget
  intro start hstart L hL
  have hbudget' := hnBudget L hL
  have hpow : width n ^ (2 : ℝ) = width n ^ (2 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hpow] at hbudget'
  exact hbudget'.trans (hnPower start hstart)

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
