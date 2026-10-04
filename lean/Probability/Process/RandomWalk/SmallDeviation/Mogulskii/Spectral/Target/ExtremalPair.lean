/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.Coefficient
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.SurvivalBounds

/-!
# The extremal spectral pair

The killed Rademacher kernel has period two.  Its first and last Dirichlet
modes have eigenvalues of equal absolute value and opposite sign.  Sharp
terminal-target estimates must keep this pair together and bound only the
remaining modes as an error.
-/

open scoped BigOperators Matrix

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The first and reversed-first modes are distinct when the interval has at
least two interior sites. -/
theorem intervalFirstMode_rev_ne {interiorCount : ℕ}
    (hcount : 1 < interiorCount) :
    (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev ≠
      ⟨0, Nat.zero_lt_of_lt hcount⟩ := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [Fin.val_rev] at hval
  omega

/-- Reflection of the first Dirichlet sine mode changes its sign according
to the parity of the lattice site. -/
theorem intervalSineMode_rev_first_apply
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (site : Fin interiorCount) :
    intervalSineMode interiorCount
        (⟨0, hcount⟩ : Fin interiorCount).rev site =
      (-1 : ℝ) ^ site.val *
        intervalSineMode interiorCount ⟨0, hcount⟩ site := by
  let first : Fin interiorCount := ⟨0, hcount⟩
  have hfreq := intervalModeFrequency_rev (interiorCount := interiorCount)
    first
  change Real.sin (intervalModeFrequency interiorCount first.rev *
        ((site.val + 1 : ℕ) : ℝ)) =
    (-1 : ℝ) ^ site.val * Real.sin
      (intervalModeFrequency interiorCount first *
        ((site.val + 1 : ℕ) : ℝ))
  rw [hfreq, intervalModeFrequency_zero hcount]
  let k : ℕ := site.val + 1
  let θ : ℝ := Real.pi / ((interiorCount + 1 : ℕ) : ℝ)
  have hk : (site.val + 1 : ℕ) = k := rfl
  rw [hk]
  have harg : (Real.pi - θ) * (k : ℝ) =
      (k : ℝ) * Real.pi - θ * (k : ℝ) := by ring
  rw [harg, Real.sin_nat_mul_pi_sub]
  have hsign : -((-1 : ℝ) ^ k * Real.sin (θ * (k : ℝ))) =
      (-1 : ℝ) ^ site.val * Real.sin (θ * (k : ℝ)) := by
    dsimp [k]
    rw [pow_succ]
    ring
  simpa [θ] using hsign

/-- The first principal coefficient of the reflected mode is the alternating
ground-state sum over the terminal target. -/
theorem intervalSineBasis_repr_targetIndicator_rev_first
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (target : Finset (Fin interiorCount)) :
    (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target)
        (⟨0, hcount⟩ : Fin interiorCount).rev =
      2 * (∑ i ∈ target,
        (-1 : ℝ) ^ i.val * intervalSineWeight interiorCount i) /
        ((interiorCount + 1 : ℕ) : ℝ) := by
  rw [intervalSineBasis_repr_eq_two_mul_dotProduct_div,
    intervalSineMode_dotProduct_targetIndicator]
  apply congrArg (fun z : ℝ => 2 * z /
    ((interiorCount + 1 : ℕ) : ℝ))
  apply Finset.sum_congr rfl
  intro i hi
  calc
    intervalSineMode interiorCount
        (⟨0, hcount⟩ : Fin interiorCount).rev i =
      (-1 : ℝ) ^ i.val * intervalSineMode interiorCount
        ⟨0, hcount⟩ i :=
      intervalSineMode_rev_first_apply hcount i
    _ = (-1 : ℝ) ^ i.val * intervalSineWeight interiorCount i := by
      rw [intervalSineMode_zero hcount]

/-- The extremal pair contributes only to terminal sites with the parity
allowed by the walk; on those sites both modes add with the same sign. -/
theorem intervalExtremalPair_factor
    (n startVal finishVal : ℕ) :
    1 + (-1 : ℝ) ^ n * (-1 : ℝ) ^ startVal * (-1 : ℝ) ^ finishVal =
      if Even (n + startVal + finishVal) then 2 else 0 := by
  have hpow : (-1 : ℝ) ^ n * (-1 : ℝ) ^ startVal *
      (-1 : ℝ) ^ finishVal = (-1 : ℝ) ^ (n + startVal + finishVal) := by
    rw [← pow_add, ← pow_add]
  rw [hpow]
  by_cases h : Even (n + startVal + finishVal)
  · simp only [h.neg_one_pow, ite_eq_left h]
    norm_num
  · have hodd : Odd (n + startVal + finishVal) := Nat.not_even_iff_odd.mp h
    simp only [hodd.neg_one_pow, ite_eq_right h]
    norm_num

/-- Terminal sites in a target that have the parity reachable from the given
starting site after `n` steps. -/
def intervalParityCompatibleTarget {interiorCount : ℕ}
    (n : ℕ) (start : Fin interiorCount)
    (target : Finset (Fin interiorCount)) : Finset (Fin interiorCount) :=
  target.filter fun finish => Even (n + start.val + finish.val)

/-- Summing the extremal parity factors over a target keeps exactly the
reachable parity class. -/
theorem sum_extremalFactor_mul_eq_two_mul_parityFilter
    {interiorCount : ℕ} (n startVal : ℕ)
    (target : Finset (Fin interiorCount)) (f : Fin interiorCount → ℝ) :
    (∑ finish ∈ target, f finish) +
        (-1 : ℝ) ^ n * (-1 : ℝ) ^ startVal *
          (∑ finish ∈ target, (-1 : ℝ) ^ finish.val * f finish) =
      2 * ∑ finish ∈ target.filter
          (fun finish => Even (n + startVal + finish.val)), f finish := by
  classical
  let compatible : Fin (interiorCount) → Prop := fun finish =>
    Even (n + startVal + finish.val)
  calc
    _ = ∑ finish ∈ target,
        (f finish +
          ((-1 : ℝ) ^ n * (-1 : ℝ) ^ startVal) *
            ((-1 : ℝ) ^ finish.val * f finish)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ finish ∈ target,
        (f finish * (1 + (-1 : ℝ) ^ n * (-1 : ℝ) ^ startVal *
          (-1 : ℝ) ^ finish.val)) := by
      apply Finset.sum_congr rfl
      intro finish hfinish
      ring
    _ = ∑ finish ∈ target,
        (if compatible finish then 2 * f finish else 0) := by
      apply Finset.sum_congr rfl
      intro finish hfinish
      rw [show 1 + (-1 : ℝ) ^ n * (-1 : ℝ) ^ startVal *
          (-1 : ℝ) ^ finish.val =
            (if compatible finish then 2 else 0) by
        simpa [compatible] using
          intervalExtremalPair_factor n startVal finish.val]
      by_cases h : compatible finish
      · simp [h]
        ring
      · simp [h]
    _ = 2 * ∑ finish ∈ target.filter compatible, f finish := by
      rw [← Finset.sum_filter]
      rw [Finset.mul_sum]

/-- The two extremal spectral modes contribute a nonnegative amount to the
killed mass on the parity-compatible part of any terminal target. -/
theorem intervalKernel_extremalPair_eq_parityTargetMass
    {interiorCount : ℕ} (hcount : 1 < interiorCount) (n : ℕ)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
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
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev start =
      4 * (Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n) /
        ((interiorCount + 1 : ℕ) : ℝ) *
        intervalSineWeight interiorCount start *
        (∑ finish ∈ intervalParityCompatibleTarget n start target,
          intervalSineWeight interiorCount finish) := by
  let first : Fin interiorCount := ⟨0, Nat.zero_lt_of_lt hcount⟩
  let q : ℝ := Real.cos (Real.pi / (interiorCount + 1 : ℕ))
  let signStart : ℝ := (-1 : ℝ) ^ start.val
  have hcoeff₀ := intervalSineBasis_repr_targetIndicator_zero
    (Nat.zero_lt_of_lt hcount) target
  have hcoeffLast := intervalSineBasis_repr_targetIndicator_rev_first
    (Nat.zero_lt_of_lt hcount) target
  have hmode₀ : intervalModeEigenvalue interiorCount first = q := by
    simp [q, first]
  have hmodeLast : intervalModeEigenvalue interiorCount first.rev = -q := by
    rw [intervalModeEigenvalue_rev, hmode₀]
  have hsineStart : intervalSineMode interiorCount first start =
      intervalSineWeight interiorCount start := by
    exact congrArg (fun f : Fin interiorCount → ℝ => f start)
      (intervalSineMode_zero (Nat.zero_lt_of_lt hcount))
  have hsineLastStart : intervalSineMode interiorCount first.rev start =
      signStart * intervalSineWeight interiorCount start := by
    rw [intervalSineMode_rev_first_apply (Nat.zero_lt_of_lt hcount) start,
      hsineStart]
  have hpow : (-q) ^ n = (-1 : ℝ) ^ n * q ^ n := by
    rw [← neg_one_mul q, mul_pow]
  rw [hmode₀, hmodeLast, hcoeff₀, hcoeffLast,
    hsineStart, hsineLastStart, hpow]
  dsimp [q, signStart, intervalParityCompatibleTarget]
  have hsum := sum_extremalFactor_mul_eq_two_mul_parityFilter
    n start.val target (intervalSineWeight interiorCount)
  calc
    _ = 2 / ((interiorCount + 1 : ℕ) : ℝ) *
        Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n *
        intervalSineWeight interiorCount start *
        ((∑ finish ∈ target, intervalSineWeight interiorCount finish) +
          (-1 : ℝ) ^ n * (-1 : ℝ) ^ start.val *
            (∑ finish ∈ target,
              (-1 : ℝ) ^ finish.val * intervalSineWeight interiorCount finish)) := by
      ring
    _ = 2 / ((interiorCount + 1 : ℕ) : ℝ) *
        Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n *
        intervalSineWeight interiorCount start *
        (2 * ∑ finish ∈ target.filter
          (fun finish => Even (n + start.val + finish.val)),
            intervalSineWeight interiorCount finish) := by rw [hsum]
    _ = _ := by ring

/-- Exact target-mass expansion with both period-two extremal modes exposed. -/
theorem intervalKernel_pow_targetMass_eq_extremalPair_add_remainder
    {interiorCount : ℕ} (hcount : 1 < interiorCount) (n : ℕ)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
    (∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish) =
      (intervalSineBasis interiorCount).repr
          (intervalTargetIndicator target)
          ⟨0, Nat.zero_lt_of_lt hcount⟩ *
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
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev start +
      ∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target) mode *
          intervalModeEigenvalue interiorCount mode ^ n *
          intervalSineMode interiorCount mode start := by
  let first : Fin interiorCount := ⟨0, Nat.zero_lt_of_lt hcount⟩
  let term : Fin interiorCount → ℝ := fun mode ↦
    (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) mode *
      intervalModeEigenvalue interiorCount mode ^ n *
      intervalSineMode interiorCount mode start
  rw [intervalKernel_pow_targetMass_eq_spectralSum]
  have hfirst : first ∈ (Finset.univ : Finset (Fin interiorCount)) :=
    Finset.mem_univ first
  have hne : first.rev ≠ first := by
    simpa [first] using intervalFirstMode_rev_ne hcount
  have hrev : first.rev ∈
      (Finset.univ : Finset (Fin interiorCount)).erase first := by
    simp [hne]
  have h₁ := Finset.add_sum_erase (Finset.univ : Finset (Fin interiorCount))
    term hfirst
  have h₂ := Finset.add_sum_erase
    ((Finset.univ : Finset (Fin interiorCount)).erase first) term hrev
  change (∑ mode, term mode) = _
  rw [← h₁, ← h₂]
  simp only [first, term, add_assoc]

/-- After retaining both extremal modes, the remaining target contribution
is controlled by the absolute eigenvalue tail over the remaining modes. -/
theorem abs_intervalKernel_targetExtremalRemainder_le
    {interiorCount : ℕ} (hcount : 1 < interiorCount) (n : ℕ)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
    |∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        (intervalSineBasis interiorCount).repr
            (intervalTargetIndicator target) mode *
          intervalModeEigenvalue interiorCount mode ^ n *
          intervalSineMode interiorCount mode start| ≤
      ∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        2 * |intervalModeEigenvalue interiorCount mode| ^ n := by
  calc
    _ ≤ ∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
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

/-- The extremal pair minus the absolute spectral tail is a lower bound for
the killed mass ending in any prescribed target. -/
theorem intervalKernel_pow_targetMass_ge_extremalPair_sub_tail
    {interiorCount : ℕ} (hcount : 1 < interiorCount) (n : ℕ)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
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
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev start -
      ∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        2 * |intervalModeEigenvalue interiorCount mode| ^ n ≤
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish := by
  let pair : ℝ :=
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
        (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev start
  let remainder : ℝ :=
    ∑ mode ∈ ((Finset.univ.erase
        (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
      (intervalSineBasis interiorCount).repr
          (intervalTargetIndicator target) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start
  let error : ℝ :=
    ∑ mode ∈ ((Finset.univ.erase
        (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
      2 * |intervalModeEigenvalue interiorCount mode| ^ n
  have hexpansion :
      (∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish) =
        pair + remainder := by
    simpa [pair, remainder] using
      intervalKernel_pow_targetMass_eq_extremalPair_add_remainder
        hcount n target start
  have habs : |remainder| ≤ error := by
    simpa [remainder, error] using
      abs_intervalKernel_targetExtremalRemainder_le hcount n target start
  have hrem : -error ≤ remainder :=
    (neg_le_neg habs).trans (neg_abs_le remainder)
  change pair - error ≤ _
  rw [hexpansion]
  linarith

/-- Removing the two extremal modes removes exactly the two depth-one terms
from the mode-depth sum. -/
theorem two_mul_add_sum_pow_intervalModeDepth_erase_extremal
    {interiorCount : ℕ} (hcount : 1 < interiorCount) (q : ℝ) :
    2 * q +
        ∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
          q ^ intervalModeDepth mode =
      ∑ mode : Fin interiorCount, q ^ intervalModeDepth mode := by
  let first : Fin interiorCount := ⟨0, Nat.zero_lt_of_lt hcount⟩
  let value : Fin interiorCount → ℝ := fun mode ↦ q ^ intervalModeDepth mode
  have hfirst : first ∈ (Finset.univ : Finset (Fin interiorCount)) :=
    Finset.mem_univ first
  have hne : first.rev ≠ first := by
    simpa [first] using intervalFirstMode_rev_ne hcount
  have hrev : first.rev ∈
      (Finset.univ : Finset (Fin interiorCount)).erase first := by
    simp [hne]
  have h₁ := Finset.add_sum_erase (Finset.univ : Finset (Fin interiorCount))
    value hfirst
  have h₂ := Finset.add_sum_erase
    ((Finset.univ : Finset (Fin interiorCount)).erase first) value hrev
  have hdepthFirst : intervalModeDepth first = 1 := by
    simp [first, intervalModeDepth]
  have hdepthRev : intervalModeDepth first.rev = 1 := by
    rw [intervalModeDepth]
    simp [first]
  rw [← h₁, ← h₂]
  simp only [value, hdepthFirst, hdepthRev, pow_one, first]
  ring

/-- The depth-weighted tail after deleting both extremal modes starts at the
second term of the geometric progression. -/
theorem sum_pow_intervalModeDepth_erase_extremal_le
    {interiorCount : ℕ} (hcount : 1 < interiorCount)
    {q : ℝ} (hq : 0 ≤ q) :
    (∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        q ^ intervalModeDepth mode) ≤
      2 * ((∑ mode : Fin interiorCount, q ^ (mode.val + 1)) - q) := by
  have hall := sum_pow_intervalModeDepth_le_two_mul_sum interiorCount hq
  have hsplit := two_mul_add_sum_pow_intervalModeDepth_erase_extremal
    hcount q
  linarith

/-- The non-extremal spectral tail is bounded by the geometric progression
with its depth-one term removed. -/
theorem sum_two_mul_abs_intervalModeEigenvalue_pow_erase_extremal_le
    {interiorCount : ℕ} (hcount : 1 < interiorCount) (n : ℕ) :
    (∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        2 * |intervalModeEigenvalue interiorCount mode| ^ n) ≤
      4 * ((∑ mode : Fin interiorCount,
        (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^
          (mode.val + 1)) -
        Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  have hq : 0 ≤ q := (intervalEigenvalue_pos hcount).le
  have hmode : ∀ mode : Fin interiorCount,
      |intervalModeEigenvalue interiorCount mode| ^ n ≤
        (q ^ n) ^ intervalModeDepth mode := by
    intro mode
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (abs_intervalModeEigenvalue_le_pow_depth mode) n
    simpa [q, ← pow_mul, Nat.mul_comm] using h
  calc
    _ ≤ 2 * ∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        (q ^ n) ^ intervalModeDepth mode := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun mode _ ↦ mul_le_mul_of_nonneg_left
        (hmode mode) (by norm_num)
    _ ≤ 2 * (2 * ((∑ mode : Fin interiorCount,
          (q ^ n) ^ (mode.val + 1)) - q ^ n)) := by
      gcongr
      exact sum_pow_intervalModeDepth_erase_extremal_le hcount
        (pow_nonneg hq n)
    _ = _ := by simp only [q]; ring

/-- Closed geometric bound for the non-extremal target error.  At a
diffusive elapsed time its numerator carries two principal-eigenvalue
powers, while the retained extremal pair carries only one. -/
theorem sum_two_mul_abs_intervalModeEigenvalue_pow_erase_extremal_le_div
    {interiorCount n : ℕ} (hcount : 1 < interiorCount) (hn : 0 < n) :
    (∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        2 * |intervalModeEigenvalue interiorCount mode| ^ n) ≤
      4 * ((Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^ 2 /
        (1 - Real.cos
          (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n)) := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  let r : ℝ := q ^ n
  have hq₀ : 0 ≤ q := (intervalEigenvalue_pos hcount).le
  have hq₁ : q < 1 := intervalEigenvalue_lt_one (Nat.zero_lt_of_lt hcount)
  have hr₀ : 0 ≤ r := pow_nonneg hq₀ n
  have hr₁ : r < 1 := pow_lt_one₀ hq₀ hq₁ hn.ne'
  have htail := Finset.sum_range_pow_succ_sub_first_le_sq_div_one_sub
    hr₀ hr₁ interiorCount
  have heq : (∑ mode : Fin interiorCount, r ^ (mode.val + 1)) =
      ∑ i ∈ Finset.range interiorCount, r ^ (i + 1) := by
    simpa using (Fin.sum_univ_eq_sum_range
      (fun i ↦ r ^ (i + 1)) interiorCount)
  have hfinite :
      (∑ mode : Fin interiorCount, r ^ (mode.val + 1)) - r ≤
        r ^ 2 / (1 - r) := by
    rw [heq]
    exact htail
  refine (sum_two_mul_abs_intervalModeEigenvalue_pow_erase_extremal_le
    hcount n).trans ?_
  dsimp [r, q] at hfinite ⊢
  nlinarith

/-- Closed geometric form of the target-mass lower bound after retaining the
two period-two extremal modes. -/
theorem intervalKernel_pow_targetMass_ge_extremalPair_sub_geometricError
    {interiorCount n : ℕ} (hcount : 1 < interiorCount) (hn : 0 < n)
    (target : Finset (Fin interiorCount)) (start : Fin interiorCount) :
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
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev start -
      4 * ((Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^ 2 /
        (1 - Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n)) ≤
      ∑ finish ∈ target, (intervalKernel interiorCount ^ n) start finish := by
  have htail := sum_two_mul_abs_intervalModeEigenvalue_pow_erase_extremal_le_div
    hcount hn
  have hgeneric := intervalKernel_pow_targetMass_ge_extremalPair_sub_tail
    hcount n target start
  have herror :
      (∑ mode ∈ ((Finset.univ.erase
          (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)).erase
            (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount).rev),
        2 * |intervalModeEigenvalue interiorCount mode| ^ n) ≤
        4 * ((Real.cos
          (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^ 2 /
          (1 - Real.cos
            (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n)) := htail
  linarith

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
