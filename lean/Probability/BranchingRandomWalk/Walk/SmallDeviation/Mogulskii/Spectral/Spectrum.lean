import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.IntervalKernel
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Full sine spectrum of the killed interval kernel

Every discrete Dirichlet sine mode is an eigenfunction of the killed simple
symmetric transition matrix.  The principal positive mode used for survival
lower bounds is the first member of this family.
-/

open scoped Matrix

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii

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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii
