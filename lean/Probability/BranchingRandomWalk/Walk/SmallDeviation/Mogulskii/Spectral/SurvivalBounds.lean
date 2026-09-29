import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.PathSurvival
import Probability.Kernel.Survival

/-!
# Uniform survival bounds for the killed symmetric walk

The positive ground state gives bounds uniform in both the starting state and
the elapsed time.  This is the finite-interval input required by the abstract
kernel blocking lemmas.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix

namespace ProbabilityTheory.RandomWalk.Mogulskii

open ProbabilityTheory.Kernel.FiniteState

/-- On an interval with at least two interior sites, the principal killed
Rademacher eigenvalue is strictly positive. -/
theorem intervalEigenvalue_pos {interiorCount : ℕ}
    (hcount : 1 < interiorCount) :
    0 < Real.cos (Real.pi / (interiorCount + 1 : ℕ)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hnonneg : 0 ≤ Real.pi / (interiorCount + 1 : ℕ) := by positivity
    linarith [Real.pi_pos]
  · have hden : (2 : ℝ) < (interiorCount + 1 : ℕ) := by
      exact_mod_cast Nat.add_lt_add_right hcount 1
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (interiorCount + 1 : ℕ))]
    nlinarith [Real.pi_pos]

/-- The principal killed-interval eigenvalue is strictly below one. -/
theorem intervalEigenvalue_lt_one {interiorCount : ℕ}
    (hcount : 0 < interiorCount) :
    Real.cos (Real.pi / (interiorCount + 1 : ℕ)) < 1 := by
  have hangle : 0 < Real.pi / ((interiorCount + 1 : ℕ) : ℝ) := by
    positivity
  have hangleLePi : Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ≤ Real.pi := by
    have hden : (1 : ℝ) ≤ (interiorCount + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le interiorCount)
    exact div_le_self Real.pi_pos.le hden
  have hanti := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
      constructor <;> linarith [Real.pi_pos])
    (show Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ∈
        Set.Icc 0 Real.pi by exact ⟨hangle.le, hangleLePi⟩)
    hangle
  simpa using hanti

/-- The endpoint value of the sine ground state is its minimum over all
interior lattice sites. -/
theorem intervalSineWeight_endpoint_le {interiorCount : ℕ}
    (hcount : 0 < interiorCount) (i : Fin interiorCount) :
    Real.sin (Real.pi / (interiorCount + 1 : ℕ)) ≤
      intervalSineWeight interiorCount i := by
  let length : ℝ := (interiorCount + 1 : ℕ)
  let coordinate : ℝ := (i.val + 1 : ℕ)
  let base := Real.pi / length
  let x := base * coordinate
  have hlength : 0 < length := by positivity
  have hlengthTwo : (2 : ℝ) ≤ length := by
    dsimp [length]
    exact_mod_cast Nat.add_le_add_right hcount 1
  have hcoordinateOne : 1 ≤ coordinate := by
    dsimp [coordinate]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.val)
  have hcoordinateLt : coordinate < length := by
    dsimp [coordinate, length]
    exact_mod_cast Nat.add_lt_add_right i.isLt 1
  have hbasePos : 0 < base := div_pos Real.pi_pos hlength
  have hbaseLeX : base ≤ x := by
    dsimp [x]
    nlinarith
  have hxLtPi : x < Real.pi := by
    dsimp [x, base]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hlength]
    nlinarith [Real.pi_pos]
  have hxNonneg : 0 ≤ x := le_of_lt (hbasePos.trans_le hbaseLeX)
  have hbaseHalf : base ≤ Real.pi / 2 := by
    dsimp [base]
    rw [div_le_iff₀ hlength]
    nlinarith [Real.pi_pos]
  change Real.sin base ≤ Real.sin x
  by_cases hxHalf : x ≤ Real.pi / 2
  · apply Real.monotoneOn_sin
    · exact ⟨by nlinarith [Real.pi_pos, hbasePos], hbaseHalf⟩
    · exact ⟨by nlinarith [Real.pi_pos], hxHalf⟩
    · exact hbaseLeX
  · rw [← Real.sin_pi_sub x]
    apply Real.monotoneOn_sin
    · exact ⟨by nlinarith [Real.pi_pos, hbasePos], hbaseHalf⟩
    · constructor
      · nlinarith [hxLtPi]
      · nlinarith [Real.pi_pos]
    · have hxUpper : x ≤ Real.pi - base := by
        have hcoordinateLe : coordinate ≤ length - 1 := by
          have hnat : i.val + 1 ≤ interiorCount := by omega
          have hlengthSub : length - 1 = (interiorCount : ℝ) := by
            simp [length]
          rw [hlengthSub]
          dsimp [coordinate]
          exact_mod_cast hnat
        calc
          x = base * coordinate := rfl
          _ ≤ base * (length - 1) :=
            mul_le_mul_of_nonneg_left hcoordinateLe hbasePos.le
          _ = Real.pi - base := by
            dsimp [base]
            field_simp
      linarith

/-- The explicit endpoint sine weight controls every row sum and every power
of the killed interval matrix. -/
theorem intervalKernel_pow_rowSum_uniform_bounds
    {interiorCount : ℕ} (hcount : 1 < interiorCount) :
    ∀ (n : ℕ) (start : Fin interiorCount),
        Real.sin (Real.pi / (interiorCount + 1 : ℕ)) *
          Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n ≤
            ∑ finish, (intervalKernel interiorCount ^ n) start finish ∧
        (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
          Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n /
            Real.sin (Real.pi / (interiorCount + 1 : ℕ)) := by
  intro n start
  let lower := Real.sin (Real.pi / (interiorCount + 1 : ℕ))
  let eigenvalue := Real.cos (Real.pi / (interiorCount + 1 : ℕ))
  have hlowerPos : 0 < lower := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hden : (1 : ℝ) < (interiorCount + 1 : ℕ) := by
        exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_of_lt hcount)
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (interiorCount + 1 : ℕ))]
      nlinarith [Real.pi_pos]
  have hlower : ∀ i, lower ≤ intervalSineWeight interiorCount i :=
    intervalSineWeight_endpoint_le (Nat.zero_lt_of_lt hcount)
  have heigenNonneg : 0 ≤ eigenvalue := (intervalEigenvalue_pos hcount).le
  have heigenPowNonneg : 0 ≤ eigenvalue ^ n := pow_nonneg heigenNonneg n
  have hweighted := sum_pow_apply_mul_weight
    (intervalKernel interiorCount) (intervalSineWeight interiorCount)
    eigenvalue (intervalKernel_mulVec_sine interiorCount) n start
  constructor
  · calc
      lower * eigenvalue ^ n ≤
          eigenvalue ^ n * intervalSineWeight interiorCount start := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left
          (hlower start) heigenPowNonneg
      _ ≤ ∑ finish, (intervalKernel interiorCount ^ n) start finish := by
        have hbounds := pow_rowSum_bounds_of_positive_eigenfunction
          (intervalKernel interiorCount) (intervalSineWeight interiorCount)
          eigenvalue lower 1 (intervalKernel_nonneg interiorCount)
          (intervalKernel_mulVec_sine interiorCount) hlower
          (intervalSineWeight_le_one interiorCount) n start
        simpa using hbounds.2
  · calc
      (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
          (eigenvalue ^ n * intervalSineWeight interiorCount start) /
            lower := by
        apply totalMass_le_div_of_weightedMass Finset.univ
          (fun finish => (intervalKernel interiorCount ^ n) start finish)
          (intervalSineWeight interiorCount) lower
          (eigenvalue ^ n * intervalSineWeight interiorCount start)
          hlowerPos
        · intro finish _
          exact Matrix.pow_apply_nonneg (intervalKernel_nonneg interiorCount)
            n start finish
        · exact fun finish _ => hlower finish
        · exact hweighted
      _ ≤ eigenvalue ^ n / lower := by
        apply (div_le_div_iff_of_pos_right hlowerPos).2
        simpa using mul_le_mul_of_nonneg_left
          (intervalSineWeight_le_one interiorCount start) heigenPowNonneg

/-- The same explicit uniform bounds stated directly for the sub-Markov
kernel's remaining mass. -/
theorem intervalRademacherKernel_remainingMass_uniform_bounds
    {interiorCount : ℕ} (hcount : 1 < interiorCount) :
    ∀ (n : ℕ) (start : Fin interiorCount),
        ENNReal.ofReal
            (Real.sin (Real.pi / (interiorCount + 1 : ℕ)) * Real.cos
              (Real.pi / (interiorCount + 1 : ℕ)) ^ n) ≤
          Kernel.remainingMass (intervalRademacherKernel interiorCount)
            n start ∧
        Kernel.remainingMass (intervalRademacherKernel interiorCount)
            n start ≤
          ENNReal.ofReal
            (Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n /
              Real.sin (Real.pi / (interiorCount + 1 : ℕ))) := by
  intro n start
  have hbounds := intervalKernel_pow_rowSum_uniform_bounds hcount n start
  have hmass : Kernel.remainingMass
      (intervalRademacherKernel interiorCount) n start =
      ENNReal.ofReal
        (∑ finish, (intervalKernel interiorCount ^ n) start finish) := by
    unfold Kernel.remainingMass
    rw [intervalRademacherKernel_eq_ofRealMatrix,
      intervalKernel_pow_apply_univ]
  rw [hmass]
  exact ⟨ENNReal.ofReal_le_ofReal hbounds.1,
    ENNReal.ofReal_le_ofReal hbounds.2⟩

/-- The spectral bounds as bounds for the interval event under the
Rademacher random-walk process.  The starting point is an interior lattice
site; no assertion is made here for a nonintegral starting point. -/
theorem rademacherProcess_intervalProbability_uniform_bounds
    {interiorCount : ℕ} (hcount : 1 < interiorCount) (n : ℕ)
    (start : Fin interiorCount) :
    ENNReal.ofReal
        (Real.sin (Real.pi / (interiorCount + 1 : ℕ)) * Real.cos
          (Real.pi / (interiorCount + 1 : ℕ)) ^ n) ≤
      (rademacher (intervalSite start)).law
        {walk | ProcessInClosedInterval id 1 interiorCount n walk} ∧
    (rademacher (intervalSite start)).law
        {walk | ProcessInClosedInterval id 1 interiorCount n walk} ≤
      ENNReal.ofReal
        (Real.cos (Real.pi / (interiorCount + 1 : ℕ)) ^ n /
          Real.sin (Real.pi / (interiorCount + 1 : ℕ))) := by
  have hbounds :=
    intervalRademacherKernel_remainingMass_uniform_bounds hcount n start
  constructor
  · rw [← intervalRademacherKernel_pow_apply_univ_eq_rademacherProcess]
    exact hbounds.1
  · rw [← intervalRademacherKernel_pow_apply_univ_eq_rademacherProcess]
    exact hbounds.2

end ProbabilityTheory.RandomWalk.Mogulskii
