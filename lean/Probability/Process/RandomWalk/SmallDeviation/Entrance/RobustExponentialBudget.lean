/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.PowerAssembly
public import Analysis.Asymptotics.PolynomialExponential

/-!
# Exponential budget for the robust entrance event

The public theorem in this file is:

- `exists_eventually_robustTransitionProbability_ge_exp_of_transitionBounds`:
  if the two reflected transition probabilities obey their polynomial
  lower bounds, then for $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$,
  $\mathbb P(E_0^{\rm robust})\ge\exp(-\delta L/\Delta^2)$ eventually.

This is the polynomial-to-exponential comparison following the entrance
construction in Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Chapter 3, proof of Lemma 3.5. The robust
entrance construction is formalized in the preceding files of this folder.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- A polynomially small robust entrance cost is absorbed by the
exponential budget of every sufficiently long target horizon. -/
theorem exists_eventually_robustTransitionProbability_ge_exp_of_transitionBounds
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {drift alpha delta epsilon : ℝ}
    (hdrift : 0 ≤ drift) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hplus : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        (iidSequenceLaw ν
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
            (width n))).toReal)
    (hminus : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C / width n ^ (1 + alpha) ≤
        (iidSequenceLaw (ν.map fun x : ℝ => -x)
          (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
            (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
            (width n))).toReal) :
    ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc 0 (width n), ∀ L : ℕ,
        Nat.floor (width n ^ (2 + epsilon)) ≤ L →
        Real.exp (-delta * (L : ℝ) / width n ^ 2) ≤
          (iidSequenceLaw ν).real
            (robustMovingTransitionEvent
              (Asymptotics.floorBlockLength (fun k => width k ^ 2) n)
              (width n) drift start) := by
  obtain ⟨C, hC, hpower⟩ :=
    exists_eventually_robustTransitionProbability_ge_power_of_transitionBounds
      hν hsigma hwidth hdrift halpha hplus hminus
  have hbudget := hwidth.eventually
    (Asymptotics.eventually_exp_neg_horizon_le_polynomial
      hC hdelta hepsilon (p := 1 + alpha))
  filter_upwards [hpower, hbudget] with n hnPower hnBudget
  intro start hstart L hL
  have hbudget' := hnBudget L hL
  have hpow : width n ^ (2 : ℝ) = width n ^ (2 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hpow] at hbudget'
  exact hbudget'.trans (hnPower start hstart)

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
