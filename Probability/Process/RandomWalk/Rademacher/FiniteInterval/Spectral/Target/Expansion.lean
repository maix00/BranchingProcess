/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Survival.Upper

/-!
# Spectral expansion with a terminal target

The public declarations in this module are:

All names below are declarations in
`ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval`.

Write $K_N=\texttt{intervalKernel}(N)$,
$1_T(i)=\texttt{intervalTargetIndicator}(T)(i)$,
$c_k(T)=(\texttt{intervalSineBasis}(N).\texttt{repr}(1_T))_k$,
$\lambda_k=\texttt{intervalModeEigenvalue}(N,k)$, and
$\phi_k(x)=\texttt{intervalSineMode}(N,k,x)$.

- `intervalTargetIndicator` and `intervalTargetIndicator_apply` define and
  evaluate $1_T(i)=\mathbf 1_{i\in T}$.
- `intervalKernel_pow_mulVec_targetIndicator` identifies the matrix action
  as target mass,
  $(K_N^n1_T)(x)=\sum_{y\in T}K_N^n(x,y)$.
- `intervalKernel_pow_targetMass_eq_spectralSum` expands this mass in the
  finite sine basis:
  $\sum_{y\in T}K_N^n(x,y)=\sum_k c_k(1_T)\lambda_k^n\phi_k(x)$.
- `abs_intervalSineBasis_repr_targetIndicator_le_two` bounds every
  coefficient by $|c_k(1_T)|\le2$.
- `intervalKernel_pow_targetMass_eq_principal_add_remainder` splits off the
  first mode, and `abs_intervalKernel_targetNonzeroModeSum_le` bounds the
  remaining absolute contribution by
  $2\sum_{k\ne0}|\lambda_k|^n$.
- `principal_sub_nonzeroModes_le_intervalKernel_pow_targetMass` turns that
  estimate into a lower bound by the principal term minus the spectral tail.

The survival estimates use the constant-one terminal function. Return
estimates instead need the mass of an arbitrary set of terminal sites. This
file supplies that target-sensitive version without adding a second killed
kernel.
-/

open scoped BigOperators Matrix

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

/-- The real indicator of a finite collection of interval sites. -/
def intervalTargetIndicator {interiorCount : ℕ}
    (target : Finset (Fin interiorCount)) : Fin interiorCount → ℝ :=
  fun finish ↦ if finish ∈ target then 1 else 0

@[simp]
theorem intervalTargetIndicator_apply {interiorCount : ℕ}
    (target : Finset (Fin interiorCount)) (finish : Fin interiorCount) :
    intervalTargetIndicator target finish = if finish ∈ target then 1 else 0 :=
  rfl

/-- Multiplication by a target indicator is the mass ending in that target. -/
theorem intervalKernel_pow_mulVec_targetIndicator
    (interiorCount n : ℕ) (target : Finset (Fin interiorCount))
    (start : Fin interiorCount) :
    (intervalKernel interiorCount ^ n *ᵥ intervalTargetIndicator target) start =
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish := by
  classical
  rw [Matrix.mulVec, dotProduct]
  simp only [intervalTargetIndicator_apply, mul_ite, mul_one, mul_zero]
  simp

/-- Exact sine expansion of the killed mass ending in a prescribed finite
target. -/
theorem intervalKernel_pow_targetMass_eq_spectralSum
    (interiorCount n : ℕ) (target : Finset (Fin interiorCount))
    (start : Fin interiorCount) :
    (∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish) =
      ∑ mode, (intervalSineBasis interiorCount).repr
          (intervalTargetIndicator target) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start := by
  have h := congrFun (intervalKernel_pow_mulVec_eq_sum interiorCount n
    (intervalTargetIndicator target)) start
  rw [intervalKernel_pow_mulVec_targetIndicator] at h
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using h

/-- A target-indicator sine coefficient is bounded uniformly by two.  The
bound deliberately ignores the target cardinality; this makes it stable as
the lattice interval grows. -/
theorem abs_intervalSineBasis_repr_targetIndicator_le_two
    (interiorCount : ℕ) (target : Finset (Fin interiorCount))
    (mode : Fin interiorCount) :
    |(intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) mode| ≤ 2 := by
  rw [intervalSineBasis_repr_eq_two_mul_dotProduct_div, abs_div, abs_mul]
  norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (interiorCount + 1 : ℕ) by positivity)]
  have hwidth : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  rw [div_le_iff₀ hwidth]
  have hdot :
      |intervalSineMode interiorCount mode ⬝ᵥ
          intervalTargetIndicator target| ≤ target.card := by
    rw [dotProduct]
    calc
      |∑ i, intervalSineMode interiorCount mode i *
          intervalTargetIndicator target i| ≤
          ∑ i, |intervalSineMode interiorCount mode i *
            intervalTargetIndicator target i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ target, |intervalSineMode interiorCount mode i| := by
        classical
        simp only [intervalTargetIndicator, mul_ite, mul_one, mul_zero,
          abs_ite, abs_zero]
        rw [← Finset.sum_filter]
        simp
      _ ≤ ∑ _i ∈ target, (1 : ℝ) := by
        exact Finset.sum_le_sum fun i _ ↦ by
          simpa only [intervalSineMode] using
            Real.abs_sin_le_one
              (intervalModeFrequency interiorCount mode * (i.val + 1 : ℕ))
      _ = target.card := by simp
  have hcard : (target.card : ℝ) ≤ interiorCount := by
    exact_mod_cast (show target.card ≤ interiorCount by
      simpa using target.card_le_univ)
  have hcount : (interiorCount : ℝ) ≤ (interiorCount + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ interiorCount
  nlinarith

/-- The target mass splits into its positive principal Dirichlet mode and
the sum of all nonzero-index modes.  The latter still contains the negative
extremal mode of the period-two Rademacher kernel; aperiodic estimates must
separate that mode as well. -/
theorem intervalKernel_pow_targetMass_eq_principal_add_remainder
    {interiorCount : ℕ} (hcount : 0 < interiorCount) (n : ℕ)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
    (∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish) =
      (intervalSineBasis interiorCount).repr
          (intervalTargetIndicator target) ⟨0, hcount⟩ *
        intervalModeEigenvalue interiorCount ⟨0, hcount⟩ ^ n *
        intervalSineMode interiorCount ⟨0, hcount⟩ start +
      ∑ mode ∈ (Finset.univ.erase ⟨0, hcount⟩),
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target) mode *
          intervalModeEigenvalue interiorCount mode ^ n *
          intervalSineMode interiorCount mode start := by
  rw [intervalKernel_pow_targetMass_eq_spectralSum]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hcount⟩ :
    Fin interiorCount))]

/-- The absolute nonzero-mode sum in the target expansion is controlled by
twice the sum of the corresponding absolute eigenvalue powers. -/
theorem abs_intervalKernel_targetNonzeroModeSum_le
    {interiorCount : ℕ} (hcount : 0 < interiorCount) (n : ℕ)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
    |∑ mode ∈ (Finset.univ.erase ⟨0, hcount⟩),
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target) mode *
          intervalModeEigenvalue interiorCount mode ^ n *
          intervalSineMode interiorCount mode start| ≤
      ∑ mode ∈ (Finset.univ.erase ⟨0, hcount⟩),
        2 * |intervalModeEigenvalue interiorCount mode| ^ n := by
  calc
    _ ≤ ∑ mode ∈ (Finset.univ.erase ⟨0, hcount⟩),
        |(intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target) mode *
          intervalModeEigenvalue interiorCount mode ^ n *
          intervalSineMode interiorCount mode start| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro mode _
      rw [abs_mul, abs_mul, abs_pow]
      have hcoeff := abs_intervalSineBasis_repr_targetIndicator_le_two
        interiorCount target mode
      have hsine : |intervalSineMode interiorCount mode start| ≤ 1 := by
        simpa only [intervalSineMode] using
          Real.abs_sin_le_one
            (intervalModeFrequency interiorCount mode * (start.val + 1 : ℕ))
      calc
        |(intervalSineBasis interiorCount).repr
              (intervalTargetIndicator target) mode| *
            |intervalModeEigenvalue interiorCount mode| ^ n *
            |intervalSineMode interiorCount mode start| ≤
          (2 * |intervalModeEigenvalue interiorCount mode| ^ n) *
            |intervalSineMode interiorCount mode start| := by gcongr
        _ ≤ (2 * |intervalModeEigenvalue interiorCount mode| ^ n) * 1 := by
          gcongr
        _ = 2 * |intervalModeEigenvalue interiorCount mode| ^ n := by ring

/-- The positive principal mode minus the absolute nonzero-mode bound is a
valid, though generally non-sharp, lower bound.  For the period-two
Rademacher kernel the negative extremal mode must subsequently be retained
together with the positive one to obtain a useful sharp bound. -/
theorem principal_sub_nonzeroModes_le_intervalKernel_pow_targetMass
    {interiorCount : ℕ} (hcount : 0 < interiorCount) (n : ℕ)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
    (intervalSineBasis interiorCount).repr
          (intervalTargetIndicator target) ⟨0, hcount⟩ *
        intervalModeEigenvalue interiorCount ⟨0, hcount⟩ ^ n *
        intervalSineMode interiorCount ⟨0, hcount⟩ start -
      ∑ mode ∈ (Finset.univ.erase ⟨0, hcount⟩),
        2 * |intervalModeEigenvalue interiorCount mode| ^ n ≤
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish := by
  let principal : ℝ :=
    (intervalSineBasis interiorCount).repr
          (intervalTargetIndicator target) ⟨0, hcount⟩ *
        intervalModeEigenvalue interiorCount ⟨0, hcount⟩ ^ n *
        intervalSineMode interiorCount ⟨0, hcount⟩ start
  let remainder : ℝ :=
    ∑ mode ∈ (Finset.univ.erase ⟨0, hcount⟩),
      (intervalSineBasis interiorCount).repr
          (intervalTargetIndicator target) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start
  let error : ℝ :=
    ∑ mode ∈ (Finset.univ.erase ⟨0, hcount⟩),
      2 * |intervalModeEigenvalue interiorCount mode| ^ n
  have hexpansion :
      (∑ finish ∈ target,
          (intervalKernel interiorCount ^ n) start finish) =
        principal + remainder := by
    simpa [principal, remainder] using
      intervalKernel_pow_targetMass_eq_principal_add_remainder
        hcount n target start
  have habs : |remainder| ≤ error := by
    simpa [remainder, error] using
      abs_intervalKernel_targetNonzeroModeSum_le hcount n target start
  have hneg : -error ≤ remainder :=
    (neg_le_neg habs).trans (neg_abs_le remainder)
  change principal - error ≤ _
  rw [hexpansion]
  linarith

end ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval
