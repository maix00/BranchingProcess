/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.RobustExponentialBudget
public import Analysis.Asymptotics.SequentialEventually

/-!
# Uniform real-width budget for the robust entrance

The public theorem in this file is:

- `eventually_robustTransitionProbability_ge_exp_of_transitionBounds`:
  if the reflected transition bounds hold along every divergent real-width
  sequence, then one threshold $\Delta_0$ works for every real
  $\Delta\ge\Delta_0$, every $x\in[0,\Delta]$, and every
  $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$:
  $\mathbb P_x(E_0^{\rm robust})\ge\exp(-\delta L/\Delta^2)$.

This is the real-width quantifier required by Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The sequential transition bounds use
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Theorem 3.2, and the Brownian-meander
identification in Caravenna--Chaumont, *Invariance principles for random
walks conditioned to stay positive*, equation (3.3). Their survival-power
bound follows from the finite coefficient recurrence in Bauer--Godrèche--Luck,
*Statistics of persistent events in the binomial random walk: Will the
drunken sailor hit the sober man?*, Appendix A, equation (A.7).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- Sequential robust-entrance bounds for arbitrary real widths imply a
single threshold valid for every sufficiently large real width. -/
theorem eventually_robustTransitionProbability_ge_exp_of_transitionBounds
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {drift alpha delta epsilon : ℝ}
    (hdrift : 0 ≤ drift) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hplus : ∀ (width : ℕ → ℝ), Tendsto width atTop atTop →
      ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
        C / width n ^ (1 + alpha) ≤
          (iidSequenceLaw ν
            (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
              (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
              (width n))).toReal)
    (hminus : ∀ (width : ℕ → ℝ), Tendsto width atTop atTop →
      ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
        C / width n ^ (1 + alpha) ≤
          (iidSequenceLaw (ν.map fun x : ℝ => -x)
            (FunctionalLimit.Conditioned.nonnegativeTransitionEvent
              (Asymptotics.floorBlockLength (fun k => width k ^ 2) n - m)
              (width n))).toReal) :
    ∀ᶠ Delta : ℝ in atTop,
      ∀ start ∈ Set.Icc 0 Delta, ∀ L : ℕ,
        Nat.floor (Delta ^ (2 + epsilon)) ≤ L →
        Real.exp (-delta * (L : ℝ) / Delta ^ 2) ≤
          (iidSequenceLaw ν).real
            (robustMovingTransitionEvent
              ⌊Delta ^ 2⌋₊ Delta drift start) := by
  apply Asymptotics.eventually_atTop_of_forall_tendsto_nat
  intro width hwidth
  have hseq :=
    exists_eventually_robustTransitionProbability_ge_exp_of_transitionBounds
      hν hsigma hwidth hdrift halpha hdelta hepsilon
      (hplus width hwidth) (hminus width hwidth)
  filter_upwards [hseq] with n hn
  simpa [Asymptotics.floorBlockLength] using hn

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
