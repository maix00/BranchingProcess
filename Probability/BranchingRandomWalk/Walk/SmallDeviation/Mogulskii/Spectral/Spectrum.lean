import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.IntervalKernel
import LinearAlgebra.Spectrum.DiagonalBasis
import Analysis.SpecialFunctions.Trigonometric.FiniteSum
import Analysis.SpecialFunctions.Trigonometric.PowerBound
import Analysis.SpecificLimits.Geometric
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Fin.Rev

/-!
# Full sine spectrum of the killed interval kernel

Every discrete Dirichlet sine mode is an eigenfunction of the killed simple
symmetric transition matrix.  The principal positive mode used for survival
lower bounds is the first member of this family.
-/

open scoped Matrix

namespace ProbabilityTheory.RandomWalk.Mogulskii

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

/-- The coordinate of a vector in the sine basis is characterized by its
dot product with the corresponding mode.  This form avoids choosing a
normalization for the orthogonal basis. -/
theorem intervalSineBasis_repr_mul_selfDot (interiorCount : ℕ)
    (f : Fin interiorCount → ℝ) (mode : Fin interiorCount) :
    (intervalSineBasis interiorCount).repr f mode *
        (intervalSineMode interiorCount mode ⬝ᵥ
          intervalSineMode interiorCount mode) =
      intervalSineMode interiorCount mode ⬝ᵥ f := by
  classical
  conv_rhs => rw [← (intervalSineBasis interiorCount).sum_repr f]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul, intervalSineBasis_apply]
  rw [Finset.sum_eq_single mode]
  · intro other _ hother
    have horth := intervalSineMode_dotProduct_eq_zero
      (interiorCount := interiorCount) (mode₁ := mode) (mode₂ := other)
      (Ne.symm hother)
    simp [horth]
  · simp

theorem intervalSineMode_selfDot_pos {interiorCount : ℕ}
    (mode : Fin interiorCount) :
    0 < intervalSineMode interiorCount mode ⬝ᵥ
      intervalSineMode interiorCount mode := by
  have hnonneg : 0 ≤ intervalSineMode interiorCount mode ⬝ᵥ
      intervalSineMode interiorCount mode := by
    exact Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (intervalSineMode interiorCount mode i)
  have hne : intervalSineMode interiorCount mode ⬝ᵥ
      intervalSineMode interiorCount mode ≠ 0 :=
    fun hzero => intervalSineMode_ne_zero mode
      ((dotProduct_self_eq_zero).mp hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Every discrete Dirichlet sine mode has the same squared norm. -/
theorem intervalSineMode_selfDot (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    intervalSineMode interiorCount mode ⬝ᵥ
        intervalSineMode interiorCount mode =
      ((interiorCount + 1 : ℕ) : ℝ) / 2 := by
  have h := Real.sum_sin_sq_mul_pi_div_succ
    interiorCount (mode.val + 1) (by omega) (by omega)
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [dotProduct, intervalSineMode, intervalModeFrequency,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, sq] using h

/-- Explicit orthogonal-coordinate formula for the (not yet normalized)
Dirichlet sine basis. -/
theorem intervalSineBasis_repr_eq_dotProduct_div (interiorCount : ℕ)
    (f : Fin interiorCount → ℝ) (mode : Fin interiorCount) :
    (intervalSineBasis interiorCount).repr f mode =
      (intervalSineMode interiorCount mode ⬝ᵥ f) /
        (intervalSineMode interiorCount mode ⬝ᵥ
          intervalSineMode interiorCount mode) := by
  apply (eq_div_iff (intervalSineMode_selfDot_pos mode).ne').2
  exact intervalSineBasis_repr_mul_selfDot interiorCount f mode

/-- The normalized coordinate formula with the common Dirichlet sine norm
made explicit. -/
theorem intervalSineBasis_repr_eq_two_mul_dotProduct_div (interiorCount : ℕ)
    (f : Fin interiorCount → ℝ) (mode : Fin interiorCount) :
    (intervalSineBasis interiorCount).repr f mode =
      2 * (intervalSineMode interiorCount mode ⬝ᵥ f) /
        ((interiorCount + 1 : ℕ) : ℝ) := by
  rw [intervalSineBasis_repr_eq_dotProduct_div,
    intervalSineMode_selfDot]
  have hwidth : (((interiorCount + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem abs_intervalSineMode_dotProduct_one_le (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    |intervalSineMode interiorCount mode ⬝ᵥ (fun _ => (1 : ℝ))| ≤
      interiorCount := by
  rw [dotProduct]
  simp only [mul_one]
  calc
    |∑ i, intervalSineMode interiorCount mode i| ≤
        ∑ i, |intervalSineMode interiorCount mode i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin interiorCount, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => by
        simpa only [intervalSineMode] using
          Real.abs_sin_le_one
            (intervalModeFrequency interiorCount mode * (i.val + 1 : ℕ))
    _ = interiorCount := by simp

/-- The sine coefficient of the constant-one vector is uniformly bounded,
independently of the interval width and the mode. -/
theorem abs_intervalSineBasis_repr_one_le_two (interiorCount : ℕ)
    (mode : Fin interiorCount) :
    |(intervalSineBasis interiorCount).repr (fun _ => (1 : ℝ)) mode| ≤ 2 := by
  rw [intervalSineBasis_repr_eq_two_mul_dotProduct_div, abs_div, abs_mul]
  norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (interiorCount + 1 : ℕ) by positivity)]
  have hwidth : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  rw [div_le_iff₀ hwidth]
  have hdot := abs_intervalSineMode_dotProduct_one_le interiorCount mode
  have hcount : (interiorCount : ℝ) ≤ (interiorCount + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ interiorCount
  nlinarith

/-- Exact finite spectral expansion of an arbitrary function under an
iterate of the killed interval endomorphism. -/
theorem intervalKernelEnd_pow_apply_eq_sum (interiorCount n : ℕ)
    (f : Fin interiorCount → ℝ) :
    (intervalKernelEnd interiorCount ^ n) f =
      ∑ mode, ((intervalSineBasis interiorCount).repr f mode *
          intervalModeEigenvalue interiorCount mode ^ n) •
        intervalSineMode interiorCount mode := by
  simpa only [intervalSineBasis_apply] using
    Module.End.pow_apply_eq_sum_repr_smul
      (intervalKernelEnd interiorCount)
      (intervalSineBasis interiorCount)
      (intervalModeEigenvalue interiorCount)
      (fun mode => by simpa using
        hasEigenvector_intervalSineMode mode) n f

theorem intervalKernel_pow_mulVecLin (interiorCount n : ℕ) :
    (intervalKernel interiorCount ^ n).mulVecLin =
      intervalKernelEnd interiorCount ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.mulVecLin_one,
        Module.End.one_eq_id]
  | succ n ih =>
      rw [pow_succ, Matrix.mulVecLin_mul, ih, pow_succ,
        Module.End.mul_eq_comp]
      rfl

/-- Matrix form of the exact finite spectral expansion. -/
theorem intervalKernel_pow_mulVec_eq_sum (interiorCount n : ℕ)
    (f : Fin interiorCount → ℝ) :
    intervalKernel interiorCount ^ n *ᵥ f =
      ∑ mode, ((intervalSineBasis interiorCount).repr f mode *
          intervalModeEigenvalue interiorCount mode ^ n) •
        intervalSineMode interiorCount mode := by
  rw [← Matrix.mulVecLin_apply, intervalKernel_pow_mulVecLin]
  exact intervalKernelEnd_pow_apply_eq_sum interiorCount n f

/-- Exact spectral expansion of the surviving row mass. -/
theorem intervalKernel_pow_rowSum_eq_spectralSum (interiorCount n : ℕ)
    (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) =
      ∑ mode, (intervalSineBasis interiorCount).repr
          (fun _ => (1 : ℝ)) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start := by
  have h := congrFun (intervalKernel_pow_mulVec_eq_sum interiorCount n
    (fun _ => (1 : ℝ))) start
  simpa only [Matrix.mulVec, dotProduct, mul_one, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_assoc] using h

/-- A width-uniform coefficient bound reduces the survival upper estimate
to a finite sum of absolute eigenvalue powers. -/
theorem intervalKernel_pow_rowSum_le_two_mul_sum_absEigenvaluePow
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
      ∑ mode, 2 * |intervalModeEigenvalue interiorCount mode| ^ n := by
  rw [intervalKernel_pow_rowSum_eq_spectralSum]
  calc
    (∑ mode, (intervalSineBasis interiorCount).repr
          (fun _ => (1 : ℝ)) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start) ≤
        |∑ mode, (intervalSineBasis interiorCount).repr
            (fun _ => (1 : ℝ)) mode *
          intervalModeEigenvalue interiorCount mode ^ n *
          intervalSineMode interiorCount mode start| := le_abs_self _
    _ ≤ ∑ mode, |(intervalSineBasis interiorCount).repr
          (fun _ => (1 : ℝ)) mode *
        intervalModeEigenvalue interiorCount mode ^ n *
        intervalSineMode interiorCount mode start| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ mode, 2 * |intervalModeEigenvalue interiorCount mode| ^ n := by
      apply Finset.sum_le_sum
      intro mode _
      rw [abs_mul, abs_mul, abs_pow]
      have hcoeff := abs_intervalSineBasis_repr_one_le_two
        interiorCount mode
      have hmode : |intervalSineMode interiorCount mode start| ≤ 1 := by
        simpa only [intervalSineMode] using
          Real.abs_sin_le_one (intervalModeFrequency interiorCount mode *
            (start.val + 1 : ℕ))
      calc
        |(intervalSineBasis interiorCount).repr
              (fun _ => (1 : ℝ)) mode| *
            |intervalModeEigenvalue interiorCount mode| ^ n *
            |intervalSineMode interiorCount mode start| ≤
          (2 * |intervalModeEigenvalue interiorCount mode| ^ n) *
            |intervalSineMode interiorCount mode start| := by
              gcongr
        _ ≤ (2 * |intervalModeEigenvalue interiorCount mode| ^ n) * 1 := by
          gcongr
        _ = 2 * |intervalModeEigenvalue interiorCount mode| ^ n := by ring

/-- The surviving row mass is bounded by a finite geometric progression in
the elapsed-time power of the principal eigenvalue.  Its prefactor is
independent of the interval width. -/
theorem intervalKernel_pow_rowSum_le_geometric {interiorCount : ℕ}
    (hcount : 0 < interiorCount) (n : ℕ) (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
      4 * ∑ mode : Fin interiorCount,
        (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n) ^
          (mode.val + 1) := by
  exact (intervalKernel_pow_rowSum_le_two_mul_sum_absEigenvaluePow
    interiorCount n start).trans
      (sum_two_mul_abs_intervalModeEigenvalue_pow_le_geometric hcount n)

/-- Closed-form, width-uniform upper bound for the surviving row mass. -/
theorem intervalKernel_pow_rowSum_le_four_mul_div_one_sub
    {interiorCount n : ℕ} (hcount : 0 < interiorCount) (hn : 0 < n)
    (start : Fin interiorCount) :
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
      4 * (Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ n /
        (1 - Real.cos (Real.pi /
          ((interiorCount + 1 : ℕ) : ℝ)) ^ n)) := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  have hwidth : (2 : ℝ) ≤ ((interiorCount + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hcount
  have hanglePos : 0 < Real.pi / ((interiorCount + 1 : ℕ) : ℝ) := by
    positivity
  have hangleLeHalf : Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ≤
      Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hwidth
  have hq₀ : 0 ≤ q := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith [Real.pi_pos]
    · exact hangleLeHalf
  have hq₁ : q < 1 := by
    have hanti := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [Real.pi_pos])
      (show Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ∈
          Set.Icc 0 Real.pi by
        constructor
        · exact hanglePos.le
        · exact hangleLeHalf.trans (by linarith [Real.pi_pos]))
      hanglePos
    simpa [q] using hanti
  have hgeom := Finset.sum_range_pow_succ_le_div_one_sub
    (pow_nonneg hq₀ n) (pow_lt_one₀ hq₀ hq₁ hn.ne') interiorCount
  calc
    (∑ finish, (intervalKernel interiorCount ^ n) start finish) ≤
        4 * ∑ mode : Fin interiorCount, (q ^ n) ^ (mode.val + 1) := by
      simpa [q] using intervalKernel_pow_rowSum_le_geometric hcount n start
    _ = 4 * ∑ i ∈ Finset.range interiorCount, (q ^ n) ^ (i + 1) := by
      congr 1
      simpa using (Fin.sum_univ_eq_sum_range
        (fun i => (q ^ n) ^ (i + 1)) interiorCount)
    _ ≤ 4 * (q ^ n / (1 - q ^ n)) :=
      mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = _ := by rfl

end ProbabilityTheory.RandomWalk.Mogulskii
