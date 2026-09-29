import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Target.Coefficient
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.SurvivalBounds

/-!
# The extremal spectral pair

The killed Rademacher kernel has period two.  Its first and last Dirichlet
modes have eigenvalues of equal absolute value and opposite sign.  Sharp
terminal-target estimates must keep this pair together and bound only the
remaining modes as an error.
-/

open scoped BigOperators Matrix

namespace ProbabilityTheory.RandomWalk.Mogulskii

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

end ProbabilityTheory.RandomWalk.Mogulskii
