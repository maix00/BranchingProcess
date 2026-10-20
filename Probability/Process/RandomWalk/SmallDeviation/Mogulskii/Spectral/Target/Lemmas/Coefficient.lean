/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.Expansion

/-!
# Coefficient estimates for spectral target proofs

The following proof-chain lemmas estimate the sine-basis coefficients of a
finite target. They are used by the extremal-mode estimate in the parent
`Target/` directory and do not form a separate user-facing interface.

All names below are declarations in
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii`.

For $N=\texttt{interiorCount}>0$, write
$\phi_0(i)=\texttt{intervalSineWeight}(N,i)$ and
$c_0(T)=(\texttt{intervalSineBasis}(N).\texttt{repr}(1_T))_0$.

- `intervalSineMode_dotProduct_targetIndicator` identifies the pairing with
  an indicator as a sum over the target:
  $\langle\phi_k,1_T\rangle=\sum_{i\in T}\phi_k(i)$.
- `intervalSineBasis_repr_targetIndicator_zero` gives the principal
  coefficient
  $c_0(1_T)=\frac{2}{N+1}\sum_{i\in T}\phi_N(i)$, where
  $\phi_N(i)=\sin(\pi(i.val+1)/(N+1))$ and $N>0$.
- `two_mul_mul_card_div_le_intervalSineBasis_repr_targetIndicator_zero`
  proves $\frac{2a|T|}{N+1}\le c_0(1_T)$ if $a\le\phi_N(i)$ on $T$.
- `two_mul_mul_le_intervalSineBasis_repr_targetIndicator_zero` gives the
  width-independent form $2ap\le c_0(1_T)$ when
  $a\ge0$, $a\le\phi_N(i)$ on $T$, and $p(N+1)\le|T|$.

The first Dirichlet coefficient of a terminal target is the normalized sum
of the positive ground state over that target. A target occupying a fixed
fraction of an interior region therefore has a coefficient bounded away
from zero uniformly in the lattice width.
-/

open scoped BigOperators Matrix

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Pairing a sine mode with a target indicator restricts the sum to the
target. -/
lemma intervalSineMode_dotProduct_targetIndicator
    {interiorCount : ℕ} (mode : Fin interiorCount)
    (target : Finset (Fin interiorCount)) :
    intervalSineMode interiorCount mode ⬝ᵥ intervalTargetIndicator target =
      ∑ i ∈ target, intervalSineMode interiorCount mode i := by
  classical
  rw [dotProduct]
  simp only [intervalTargetIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

/-- The first sine-basis coefficient is the normalized ground-state mass of
the terminal target. -/
lemma intervalSineBasis_repr_targetIndicator_zero
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (target : Finset (Fin interiorCount)) :
    (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) ⟨0, hcount⟩ =
      2 * (∑ i ∈ target, intervalSineWeight interiorCount i) /
        ((interiorCount + 1 : ℕ) : ℝ) := by
  rw [intervalSineBasis_repr_eq_two_mul_dotProduct_div,
    intervalSineMode_dotProduct_targetIndicator,
    intervalSineMode_zero hcount]

/-- A pointwise ground-state lower bound on the target gives a quantitative
lower bound on its principal sine coefficient. -/
lemma two_mul_mul_card_div_le_intervalSineBasis_repr_targetIndicator_zero
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (target : Finset (Fin interiorCount)) {weight : ℝ}
    (htarget : ∀ i ∈ target, weight ≤ intervalSineWeight interiorCount i) :
    2 * weight * target.card / ((interiorCount + 1 : ℕ) : ℝ) ≤
      (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) ⟨0, hcount⟩ := by
  rw [intervalSineBasis_repr_targetIndicator_zero hcount]
  have hsum : weight * target.card ≤
      ∑ i ∈ target, intervalSineWeight interiorCount i := by
    calc
      weight * target.card = ∑ _i ∈ target, weight := by
        simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i hi ↦ htarget i hi
  have hwidth : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  apply (div_le_div_iff_of_pos_right hwidth).2
  nlinarith

/-- A lower bound on both the ground-state values and the relative target
cardinality gives a width-independent positive principal coefficient. -/
lemma two_mul_mul_le_intervalSineBasis_repr_targetIndicator_zero
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (target : Finset (Fin interiorCount)) {weight proportion : ℝ}
    (hweight : 0 ≤ weight)
    (htarget : ∀ i ∈ target, weight ≤ intervalSineWeight interiorCount i)
    (hcard : proportion * ((interiorCount + 1 : ℕ) : ℝ) ≤ target.card) :
    2 * weight * proportion ≤
      (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) ⟨0, hcount⟩ := by
  refine le_trans ?_
    (two_mul_mul_card_div_le_intervalSineBasis_repr_targetIndicator_zero
      hcount target htarget)
  have hwidth : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  rw [le_div_iff₀ hwidth]
  have hmul : (2 * weight) *
        (proportion * ((interiorCount + 1 : ℕ) : ℝ)) ≤
      (2 * weight) * target.card :=
    mul_le_mul_of_nonneg_left hcard (mul_nonneg (by norm_num) hweight)
  nlinarith

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
