/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.IntervalKernel
public import LinearAlgebra.Spectrum.DiagonalBasis
public import Analysis.SpecialFunctions.Trigonometric.PowerBound
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Fin.Rev

/-!
# Dirichlet modes of the killed interval kernel

This file defines the full discrete sine family, proves the eigenfunction
identities, and constructs the orthogonal sine basis.  Spectral expansions and
row-mass estimates are kept in the dependent files.
-/

open scoped Matrix
@[expose] public section

/-! ### Principal eigenvalue signs

These facts concern the discrete Dirichlet spectrum itself.  They are kept
here so the survival layer only consumes them when deriving row-mass bounds.
-/

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Frequency of a discrete Dirichlet sine mode on an interval with
`interiorCount` interior sites. -/
noncomputable def intervalModeFrequency (interiorCount : ℕ)
    (mode : Fin interiorCount) : ℝ :=
  Real.pi * (mode.val + 1 : ℕ) / (interiorCount + 1 : ℕ)

/-- A member of the discrete Dirichlet sine family. -/
noncomputable def intervalSineMode (interiorCount : ℕ)
    (mode : Fin interiorCount) : Fin interiorCount → ℝ :=
  fun i => Real.sin
    (intervalModeFrequency interiorCount mode * (i.val + 1 : ℕ))

/-- Eigenvalue associated with a discrete Dirichlet sine mode. -/
noncomputable def intervalModeEigenvalue (interiorCount : ℕ)
    (mode : Fin interiorCount) : ℝ :=
  Real.cos (intervalModeFrequency interiorCount mode)

/-- The killed interval matrix regarded as a linear endomorphism. -/
noncomputable def intervalKernelEnd (interiorCount : ℕ) :
    Module.End ℝ (Fin interiorCount → ℝ) :=
  (intervalKernel interiorCount).mulVecLin

@[simp]
theorem intervalModeFrequency_zero {interiorCount : ℕ}
    (hcount : 0 < interiorCount) :
    intervalModeFrequency interiorCount ⟨0, hcount⟩ =
      Real.pi / (interiorCount + 1 : ℕ) := by
  simp [intervalModeFrequency]

/-- The formerly distinguished positive sine weight is exactly the first
mode of the full Dirichlet sine family. -/
theorem intervalSineMode_zero {interiorCount : ℕ}
    (hcount : 0 < interiorCount) :
    intervalSineMode interiorCount ⟨0, hcount⟩ =
      intervalSineWeight interiorCount := by
  funext i
  simp [intervalSineMode, intervalSineWeight, dirichletSine,
    intervalModeFrequency]

@[simp]
theorem intervalModeEigenvalue_zero {interiorCount : ℕ}
    (hcount : 0 < interiorCount) :
    intervalModeEigenvalue interiorCount ⟨0, hcount⟩ =
      Real.cos (Real.pi / (interiorCount + 1 : ℕ)) := by
  simp [intervalModeEigenvalue]

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

theorem intervalModeFrequency_mem_Ioo {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    intervalModeFrequency interiorCount mode ∈ Set.Ioo 0 Real.pi := by
  have hlength : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  have hmode : (0 : ℝ) < (mode.val + 1 : ℕ) := by positivity
  have hmodeLt : ((mode.val + 1 : ℕ) : ℝ) <
      (interiorCount + 1 : ℕ) := by
    exact_mod_cast Nat.add_lt_add_right mode.isLt 1
  constructor
  · exact div_pos (mul_pos Real.pi_pos hmode) hlength
  · unfold intervalModeFrequency
    rw [div_lt_iff₀ hlength]
    nlinarith [Real.pi_pos]

/-- Reversing the mode index reflects its frequency across `π / 2`. -/
theorem intervalModeFrequency_rev {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    intervalModeFrequency interiorCount mode.rev =
      Real.pi - intervalModeFrequency interiorCount mode := by
  rw [intervalModeFrequency, intervalModeFrequency]
  simp only [Fin.val_rev]
  have hmode : mode.val + 1 ≤ interiorCount := mode.isLt
  field_simp
  rw [show interiorCount - (mode.val + 1) + 1 =
      interiorCount + 1 - (mode.val + 1) by omega]
  rw [Nat.cast_sub (by omega : mode.val + 1 ≤ interiorCount + 1)]

/-- Reversing a Dirichlet mode negates its eigenvalue. -/
theorem intervalModeEigenvalue_rev {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    intervalModeEigenvalue interiorCount mode.rev =
      -intervalModeEigenvalue interiorCount mode := by
  rw [intervalModeEigenvalue, intervalModeFrequency_rev,
    Real.cos_pi_sub, intervalModeEigenvalue]

/-- Opposite Dirichlet modes have equal absolute eigenvalue. -/
theorem abs_intervalModeEigenvalue_rev {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    |intervalModeEigenvalue interiorCount mode.rev| =
      |intervalModeEigenvalue interiorCount mode| := by
  rw [intervalModeEigenvalue_rev, abs_neg]

/-- In the lower half of the spectrum, the absolute eigenvalue is bounded by
the corresponding power of the principal eigenvalue.  Together with mode
reversal, this turns the whole spectral tail into a geometric sum. -/
theorem abs_intervalModeEigenvalue_le_pow_first {interiorCount : ℕ}
    (mode : Fin interiorCount)
    (hmode : 2 * (mode.val + 1) ≤ interiorCount + 1) :
    |intervalModeEigenvalue interiorCount mode| ≤
      Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^
        (mode.val + 1) := by
  let x : ℝ := Real.pi / ((interiorCount + 1 : ℕ) : ℝ)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hmodeReal : (2 : ℝ) * ((mode.val + 1 : ℕ) : ℝ) ≤
      ((interiorCount + 1 : ℕ) : ℝ) := by
    exact_mod_cast hmode
  have hangle : ((mode.val + 1 : ℕ) : ℝ) * x ≤ Real.pi / 2 := by
    dsimp [x]
    have hwidth : (0 : ℝ) < ((interiorCount + 1 : ℕ) : ℝ) := by positivity
    rw [show ((mode.val + 1 : ℕ) : ℝ) *
        (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) =
      (((mode.val + 1 : ℕ) : ℝ) * Real.pi) /
        ((interiorCount + 1 : ℕ) : ℝ) by ring]
    rw [div_le_div_iff₀ hwidth (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hcosNonneg : 0 ≤ Real.cos (((mode.val + 1 : ℕ) : ℝ) * x) :=
    Real.cos_nonneg_of_mem_Icc ⟨by
      have hnonneg : 0 ≤ ((mode.val + 1 : ℕ) : ℝ) * x :=
        mul_nonneg (by positivity) hx
      linarith [Real.pi_pos], hangle⟩
  rw [intervalModeEigenvalue, show intervalModeFrequency interiorCount mode =
      ((mode.val + 1 : ℕ) : ℝ) * x by
    dsimp [intervalModeFrequency, x]
    ring]
  rw [abs_of_nonneg hcosNonneg]
  simpa [x] using
    (Real.cos_nat_mul_le_pow_cos hx hangle)

/-- Distance of a mode from the nearer end of the Dirichlet spectrum. -/
def intervalModeDepth {interiorCount : ℕ} (mode : Fin interiorCount) : ℕ :=
  min (mode.val + 1) (mode.rev.val + 1)

/-- Every absolute eigenvalue is controlled by a power of the principal
eigenvalue, with exponent given by the distance to the nearer spectral end. -/
theorem abs_intervalModeEigenvalue_le_pow_depth {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    |intervalModeEigenvalue interiorCount mode| ≤
      Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^
        intervalModeDepth mode := by
  have hsum : mode.val + 1 + (mode.rev.val + 1) = interiorCount + 1 := by
    simp only [Fin.val_rev]
    omega
  by_cases hle : mode.val + 1 ≤ mode.rev.val + 1
  · rw [intervalModeDepth, Nat.min_eq_left hle]
    apply abs_intervalModeEigenvalue_le_pow_first
    omega
  · have hle' : mode.rev.val + 1 ≤ mode.val + 1 :=
      Nat.le_of_lt (Nat.lt_of_not_ge hle)
    rw [intervalModeDepth, Nat.min_eq_right hle']
    rw [← abs_intervalModeEigenvalue_rev mode]
    apply abs_intervalModeEigenvalue_le_pow_first
    omega

/-- Summing by distance from the nearer spectral endpoint costs at most two
copies of the ordinary geometric progression. -/
theorem sum_pow_intervalModeDepth_le_two_mul_sum (interiorCount : ℕ)
    {q : ℝ} (hq : 0 ≤ q) :
    (∑ mode : Fin interiorCount, q ^ intervalModeDepth mode) ≤
      2 * ∑ mode : Fin interiorCount, q ^ (mode.val + 1) := by
  calc
    (∑ mode : Fin interiorCount, q ^ intervalModeDepth mode) ≤
        ∑ mode : Fin interiorCount,
          (q ^ (mode.val + 1) + q ^ (mode.rev.val + 1)) := by
      apply Finset.sum_le_sum
      intro mode _
      unfold intervalModeDepth
      by_cases hle : mode.val + 1 ≤ mode.rev.val + 1
      · rw [Nat.min_eq_left hle]
        exact le_add_of_nonneg_right (pow_nonneg hq _)
      · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hle))]
        exact le_add_of_nonneg_left (pow_nonneg hq _)
    _ = (∑ mode : Fin interiorCount, q ^ (mode.val + 1)) +
          ∑ mode : Fin interiorCount, q ^ (mode.rev.val + 1) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * ∑ mode : Fin interiorCount, q ^ (mode.val + 1) := by
      have hrev : (∑ mode : Fin interiorCount,
          q ^ (mode.rev.val + 1)) =
          ∑ mode : Fin interiorCount, q ^ (mode.val + 1) := by
        simpa using (Equiv.sum_comp Fin.revPerm
          (fun mode : Fin interiorCount => q ^ (mode.val + 1)))
      rw [hrev]
      ring

/-- The absolute spectral sum is bounded by a geometric progression whose
ratio is the elapsed-time power of the principal eigenvalue. -/
theorem sum_two_mul_abs_intervalModeEigenvalue_pow_le_geometric
    {interiorCount : ℕ} (hcount : 0 < interiorCount) (n : ℕ) :
    (∑ mode : Fin interiorCount,
        2 * |intervalModeEigenvalue interiorCount mode| ^ n) ≤
      4 * ∑ mode : Fin interiorCount,
        (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^
          (mode.val + 1) := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  have hwidth : (2 : ℝ) ≤ ((interiorCount + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hcount
  have hx : Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ≤ Real.pi / 2 := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hwidth
  have hq : 0 ≤ q := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : 0 ≤ Real.pi / ((interiorCount + 1 : ℕ) : ℝ) := by positivity
      linarith [Real.pi_pos]
    · exact hx
  calc
    (∑ mode : Fin interiorCount,
        2 * |intervalModeEigenvalue interiorCount mode| ^ n) ≤
        2 * ∑ mode : Fin interiorCount, (q ^ n) ^ intervalModeDepth mode := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro mode _
      gcongr
      have hmode := abs_intervalModeEigenvalue_le_pow_depth mode
      have hp := pow_le_pow_left₀ (abs_nonneg _) hmode n
      simpa [q, ← pow_mul, Nat.mul_comm] using hp
    _ ≤ 2 * (2 * ∑ mode : Fin interiorCount,
        (q ^ n) ^ (mode.val + 1)) := by
      gcongr
      exact sum_pow_intervalModeDepth_le_two_mul_sum interiorCount
        (pow_nonneg hq n)
    _ = 4 * ∑ mode : Fin interiorCount,
        (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^
          (mode.val + 1) := by
      dsimp [q]
      ring

theorem strictMono_intervalModeFrequency (interiorCount : ℕ) :
    StrictMono (intervalModeFrequency interiorCount) := by
  intro i j hij
  have hlength : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  rw [intervalModeFrequency, intervalModeFrequency,
    div_lt_div_iff_of_pos_right hlength]
  have hval : i.val < j.val := hij
  exact mul_lt_mul_of_pos_left
    (by exact_mod_cast Nat.add_lt_add_right hval 1) Real.pi_pos

/-- Distinct Dirichlet sine modes have distinct eigenvalues. -/
theorem injective_intervalModeEigenvalue (interiorCount : ℕ) :
    Function.Injective (intervalModeEigenvalue interiorCount) := by
  intro i j hij
  apply (strictMono_intervalModeFrequency interiorCount).injective
  apply Real.strictAntiOn_cos.injOn
    ⟨(intervalModeFrequency_mem_Ioo i).1.le,
      (intervalModeFrequency_mem_Ioo i).2.le⟩
    ⟨(intervalModeFrequency_mem_Ioo j).1.le,
      (intervalModeFrequency_mem_Ioo j).2.le⟩
  simpa only [intervalModeEigenvalue] using hij

theorem intervalLeftNeighbor_sineMode (interiorCount : ℕ)
    (mode i : Fin interiorCount) :
    (intervalLeftNeighbor i).elim 0 (intervalSineMode interiorCount mode) =
      Real.sin (intervalModeFrequency interiorCount mode * i.val) := by
  unfold intervalLeftNeighbor
  split_ifs with hi
  · simp only [Option.elim_some, intervalSineMode]
    rw [show i.val - 1 + 1 = i.val by omega]
  · have hiz : i.val = 0 := Nat.eq_zero_of_not_pos hi
    simp [hiz]

theorem intervalRightNeighbor_sineMode (interiorCount : ℕ)
    (mode i : Fin interiorCount) :
    (intervalRightNeighbor i).elim 0 (intervalSineMode interiorCount mode) =
      Real.sin
        (intervalModeFrequency interiorCount mode * (i.val + 2 : ℕ)) := by
  unfold intervalRightNeighbor
  split_ifs with hi
  · simp only [Option.elim_some, intervalSineMode]
  · have hilast : i.val + 1 = interiorCount := by omega
    simp only [Option.elim_none]
    rw [show (i.val + 2 : ℕ) = interiorCount + 1 by omega]
    have hlength : ((interiorCount + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [show intervalModeFrequency interiorCount mode *
          ((interiorCount + 1 : ℕ) : ℝ) =
        ((mode.val + 1 : ℕ) : ℝ) * Real.pi by
      simp only [intervalModeFrequency]
      field_simp]
    exact (Real.sin_nat_mul_pi (mode.val + 1)).symm

/-- Every discrete Dirichlet sine mode is an eigenfunction of the killed
interval transition matrix. -/
theorem intervalKernel_mulVec_sineMode (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    intervalKernel interiorCount *ᵥ intervalSineMode interiorCount mode =
      intervalModeEigenvalue interiorCount mode •
        intervalSineMode interiorCount mode := by
  funext i
  rw [intervalKernel_mulVec]
  rw [option_elim_mul, option_elim_mul,
    intervalLeftNeighbor_sineMode, intervalRightNeighbor_sineMode]
  have hs := symmetricStep_sine
    (intervalModeFrequency interiorCount mode) ((i.val + 1 : ℕ) : ℝ)
  simp only [symmetricStep] at hs
  have hs' :
      (Real.sin (intervalModeFrequency interiorCount mode * i.val) +
          Real.sin (intervalModeFrequency interiorCount mode *
            (i.val + 2 : ℕ))) / 2 =
        intervalModeEigenvalue interiorCount mode *
          intervalSineMode interiorCount mode i := by
    norm_num [Nat.cast_add, Nat.cast_one] at hs
    simp only [intervalModeEigenvalue, intervalSineMode,
      Nat.cast_add, Nat.cast_one]
    convert hs using 1
    all_goals ring_nf
  calc
    _ = (Real.sin (intervalModeFrequency interiorCount mode * i.val) +
          Real.sin (intervalModeFrequency interiorCount mode *
            (i.val + 2 : ℕ))) / 2 := by ring
    _ = _ := hs'

theorem intervalSineMode_ne_zero {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    intervalSineMode interiorCount mode ≠ 0 := by
  intro hzero
  have hatZero := congrFun hzero
    (⟨0, lt_of_le_of_lt (Nat.zero_le mode.val) mode.isLt⟩ :
      Fin interiorCount)
  have hfrequency := intervalModeFrequency_mem_Ioo mode
  have hsin : 0 < Real.sin (intervalModeFrequency interiorCount mode) :=
    Real.sin_pos_of_pos_of_lt_pi hfrequency.1 hfrequency.2
  simp only [intervalSineMode, Pi.zero_apply, zero_add, Nat.cast_one,
    mul_one] at hatZero
  exact hsin.ne' hatZero

/-- Distinct Dirichlet sine modes are orthogonal for the standard dot
product.  This follows abstractly from symmetry of the killed kernel and
distinctness of its mode eigenvalues. -/
theorem intervalSineMode_dotProduct_eq_zero {interiorCount : ℕ}
    {mode₁ mode₂ : Fin interiorCount} (hne : mode₁ ≠ mode₂) :
    intervalSineMode interiorCount mode₁ ⬝ᵥ
        intervalSineMode interiorCount mode₂ = 0 := by
  have hcomm := (intervalKernel_isSymm interiorCount).dotProduct_mulVec_comm
    (x := intervalSineMode interiorCount mode₁)
    (y := intervalSineMode interiorCount mode₂)
  rw [intervalKernel_mulVec_sineMode, intervalKernel_mulVec_sineMode] at hcomm
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_comm] at hcomm
  have heigen : intervalModeEigenvalue interiorCount mode₁ ≠
      intervalModeEigenvalue interiorCount mode₂ :=
    fun h => hne ((injective_intervalModeEigenvalue interiorCount) h)
  have hmul :
      (intervalModeEigenvalue interiorCount mode₁ -
          intervalModeEigenvalue interiorCount mode₂) *
        (intervalSineMode interiorCount mode₁ ⬝ᵥ
          intervalSineMode interiorCount mode₂) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hmul with hzero | hzero
  · exact (sub_ne_zero.mpr heigen hzero).elim
  · exact hzero

theorem hasEigenvector_intervalSineMode {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    (intervalKernelEnd interiorCount).HasEigenvector
      (intervalModeEigenvalue interiorCount mode)
      (intervalSineMode interiorCount mode) := by
  rw [Module.End.hasEigenvector_iff]
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change intervalKernel interiorCount *ᵥ
      intervalSineMode interiorCount mode = _
    exact intervalKernel_mulVec_sineMode interiorCount mode
  · exact intervalSineMode_ne_zero mode

/-- The complete family of Dirichlet sine modes is linearly independent. -/
theorem linearIndependent_intervalSineMode (interiorCount : ℕ) :
    LinearIndependent ℝ (intervalSineMode interiorCount) :=
  (intervalKernelEnd interiorCount).eigenvectors_linearIndependent'
    (intervalModeEigenvalue interiorCount)
    (injective_intervalModeEigenvalue interiorCount)
    (intervalSineMode interiorCount)
    hasEigenvector_intervalSineMode

/-- The Dirichlet sine family forms a basis of all real functions on the
interior sites. -/
noncomputable def intervalSineBasis (interiorCount : ℕ) :
    Module.Basis (Fin interiorCount) ℝ (Fin interiorCount → ℝ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent
    (linearIndependent_intervalSineMode interiorCount)

@[simp]
theorem intervalSineBasis_apply (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    intervalSineBasis interiorCount mode =
      intervalSineMode interiorCount mode := by
  simp [intervalSineBasis]

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
