/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.PolynomialExponential
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.DiffusiveTransitionLower
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.PowerAssembly

/-!
# Exponential budget for the robust entrance event

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.exists_eventually_robustTransitionProbability_ge_exp_of_centeredFiniteVariance`:
  for $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$, the uniform entrance bound
  $C\Delta^{-2}$ from the private entrance estimate pays an exponential cost
  at most $\exp(-\delta L/\Delta^2)$.

This is the polynomial-to-exponential comparison following the entrance
construction in Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Chapter 3, proof of Lemma 3.5. The
`Robust` support modules contain the three-region entrance construction.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The three entrance regimes yield the inverse-square bound for the
terminal window of Wang Yiyang, *Asymptotic speed of the $N$-branching
random walk with infinite offspring*, Appendix A.2, Lemma A.7. -/
private theorem exists_eventually_robustTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
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


/-- The robust entrance cost is absorbed by the exponential budget after
the meander transition has been supplied for both the walk and its
reflection. -/
theorem exists_eventually_robustTransitionProbability_ge_exp_of_centeredFiniteVariance
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
  obtain ⟨C, hC, hpower⟩ :=
    exists_eventually_robustTransitionProbability_ge_inverse_square_of_centeredFiniteVariance
      ν hν hsigma hwidth hdrift
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
