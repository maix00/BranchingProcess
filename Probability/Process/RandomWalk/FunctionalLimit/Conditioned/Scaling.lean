/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival
public import Probability.Distributions.Moments.Real

/-!
# Positive scaling of survival-conditioned random walks

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivesNonnegative_div_const_iff`:
  for $\sigma>0$, survival of $(x_j/\sigma)$ through time $n$ is
  equivalent to survival of $(x_j)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.survivalConditionedLaw_map_div`:
  the law of $(X_j/\sigma)$ conditioned on survival is the pushforward
  of the conditioned law of $(X_j)$.

This is the variance-normalization step in the conditioned invariance
principle of Erwin Bolthausen, *On a functional central limit theorem
for random walks conditioned to stay positive*, Ann. Probab. 4(3)
(1976), 480--485, Theorem 3.2, used in Wang Yiyang, Chapter 3,
proof of Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- Dividing increments by a positive constant preserves every partial
sum's sign. -/
theorem survivesNonnegative_div_const_iff
    {sigma : ℝ} (hsigma : 0 < sigma) (n : ℕ)
    (increment : ℕ → ℝ) :
    SurvivesNonnegative n (fun j => increment j / sigma) ↔
      SurvivesNonnegative n increment := by
  have hdisp (k : ℕ) :
      AdditivePath.displacement k (fun j => increment j / sigma) =
        AdditivePath.displacement k increment / sigma := by
    simp [AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
  constructor
  · intro h k
    have hk := h k
    rw [hdisp] at hk
    have hmul := mul_nonneg hk hsigma.le
    have hcancel : AdditivePath.displacement (k + 1) increment / sigma * sigma =
        AdditivePath.displacement (k + 1) increment :=
      div_mul_cancel₀ _ hsigma.ne'
    linarith
  · intro h k
    rw [hdisp]
    exact div_nonneg (h k) hsigma.le

/-- Positive spatial normalization commutes with survival conditioning. -/
theorem survivalConditionedLaw_map_div
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hsigma : 0 < sigma) (n : ℕ) :
    (survivalConditionedLaw ν n).map
      (fun x : ℕ → ℝ => fun j => x j / sigma) =
    survivalConditionedLaw (ν.map fun x => x / sigma) n := by
  let T : (ℕ → ℝ) → (ℕ → ℝ) := fun x j => x j / sigma
  let S : Set (ℕ → ℝ) := {x | SurvivesNonnegative n x}
  have hT : Measurable T :=
    Measurable.of_eval fun j =>
      (measurable_id.div_const sigma).comp (measurable_pi_apply j)
  have hS : MeasurableSet S := measurableSet_survivesNonnegative n
  have hSpre : T ⁻¹' S = S := by
    ext x
    exact survivesNonnegative_div_const_iff hsigma n x
  have hiid : (iidSequenceLaw ν).map T =
      iidSequenceLaw (ν.map fun x => x / sigma) := by
    simpa only [T] using iidSequenceLaw_map_coordinatewise ν
      (fun x => x / sigma) (measurable_id.div_const sigma)
  apply Measure.ext
  intro A hA
  have hApre : MeasurableSet (T ⁻¹' A) := hA.preimage hT
  change ((iidSequenceLaw ν)[|S]).map T A =
    ((iidSequenceLaw (ν.map fun x => x / sigma))[|S]) A
  rw [Measure.map_apply hT hA]
  rw [ProbabilityTheory.cond_apply hS (iidSequenceLaw ν) (T ⁻¹' A)]
  rw [ProbabilityTheory.cond_apply hS
    (iidSequenceLaw (ν.map fun x => x / sigma)) A]
  have hmeasureS : iidSequenceLaw ν S =
      iidSequenceLaw (ν.map fun x => x / sigma) S := by
    rw [← hiid, Measure.map_apply hT hS, hSpre]
  have hmeasureInter : iidSequenceLaw ν (S ∩ T ⁻¹' A) =
      iidSequenceLaw (ν.map fun x => x / sigma) (S ∩ A) := by
    rw [← hiid, Measure.map_apply hT (hS.inter hA)]
    congr 1
    ext x
    change (x ∈ S ∧ T x ∈ A) ↔ (T x ∈ S ∧ T x ∈ A)
    have hiff : T x ∈ S ↔ x ∈ S :=
      survivesNonnegative_div_const_iff hsigma n x
    rw [hiff]
  rw [← hmeasureS, ← hmeasureInter]

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
