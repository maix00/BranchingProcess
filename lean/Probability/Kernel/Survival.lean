import Probability.Kernel.SubMarkov
import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Remaining mass of iterated kernels

For a sub-Markov kernel, evaluation on the whole space is the probability
mass that has not been killed.  The definitions and Chapman--Kolmogorov
identities below apply to every kernel; sub-Markovness is only needed when
one wants to interpret the value as a probability.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- Total mass remaining after `n` iterations of a kernel. -/
noncomputable def remainingMass (K : Kernel S S) (n : ℕ) (start : S) : ENNReal :=
  (K ^ n) start univ

@[simp]
theorem remainingMass_zero (K : Kernel S S) (start : S) :
    remainingMass K 0 start = 1 := by
  change Kernel.id start univ = 1
  rw [Kernel.id_apply]
  simp

/-- Chapman--Kolmogorov decomposition of remaining mass into two time
blocks. -/
theorem remainingMass_add (K : Kernel S S) (m n : ℕ) (start : S) :
    remainingMass K (m + n) start =
      ∫⁻ state, remainingMass K n state ∂(K ^ m) start := by
  exact Kernel.pow_add_apply_eq_lintegral K m n start MeasurableSet.univ

/-- A uniform lower bound for the second block multiplies the mass surviving
the first block. -/
theorem mul_remainingMass_le_remainingMass_add
    (K : Kernel S S) (m n : ℕ) (start : S) (lower : ENNReal)
    (hlower : ∀ state, lower ≤ remainingMass K n state) :
    lower * remainingMass K m start ≤ remainingMass K (m + n) start := by
  rw [remainingMass_add]
  change lower * (K ^ m) start univ ≤ _
  rw [← MeasureTheory.lintegral_const]
  exact MeasureTheory.lintegral_mono hlower

/-- If the first block reaches a measurable entrance set with some mass and
the second block has a uniform survival lower bound on that set, their
product bounds the survival mass of the concatenated blocks. -/
theorem mul_pow_apply_le_remainingMass_add_of_mem
    (K : Kernel S S) (m n : ℕ) (start : S) (entrance : Set S)
    (hentrance : MeasurableSet entrance) (lower : ENNReal)
    (hlower : ∀ state ∈ entrance, lower ≤ remainingMass K n state) :
    lower * (K ^ m) start entrance ≤ remainingMass K (m + n) start := by
  rw [remainingMass_add, ← MeasureTheory.setLIntegral_const,
    ← MeasureTheory.lintegral_indicator hentrance]
  apply MeasureTheory.lintegral_mono
  intro state
  by_cases hstate : state ∈ entrance
  · simpa [hstate] using hlower state hstate
  · simp [hstate]

/-- A uniform upper bound for the second block multiplies the mass surviving
the first block. -/
theorem remainingMass_add_le_mul_remainingMass
    (K : Kernel S S) (m n : ℕ) (start : S) (upper : ENNReal)
    (hupper : ∀ state, remainingMass K n state ≤ upper) :
    remainingMass K (m + n) start ≤
      upper * remainingMass K m start := by
  rw [remainingMass_add]
  change _ ≤ upper * (K ^ m) start univ
  rw [← MeasureTheory.lintegral_const]
  exact MeasureTheory.lintegral_mono hupper

/-- A sub-Markov kernel has at most unit mass after every number of steps. -/
theorem remainingMass_le_one (K : Kernel S S) [IsSubMarkovKernel K]
    (n : ℕ) (start : S) :
    remainingMass K n start ≤ 1 := by
  unfold remainingMass
  exact IsSubMarkovKernel.measure_univ_le_one start

/-- Killing can only decrease total mass as more time blocks are appended. -/
theorem remainingMass_add_le_left (K : Kernel S S) [IsSubMarkovKernel K]
    (m n : ℕ) (start : S) :
    remainingMass K (m + n) start ≤ remainingMass K m start := by
  have h := remainingMass_add_le_mul_remainingMass
    K m n start 1 (remainingMass_le_one K n)
  simpa using h

/-- Remaining mass of a sub-Markov kernel is antitone in elapsed time. -/
theorem antitone_remainingMass (K : Kernel S S) [IsSubMarkovKernel K]
    (start : S) :
    Antitone (fun n => remainingMass K n start) := by
  intro m n hmn
  rw [show n = m + (n - m) by omega]
  exact remainingMass_add_le_left K m (n - m) start

/-- Repeating a block with a uniform lower survival bound gives the
corresponding power lower bound. -/
theorem pow_le_remainingMass_mul
    (K : Kernel S S) (block repetitions : ℕ) (start : S) (lower : ENNReal)
    (hlower : ∀ state, lower ≤ remainingMass K block state) :
    lower ^ repetitions ≤ remainingMass K (repetitions * block) start := by
  induction repetitions with
  | zero => simp
  | succ repetitions ih =>
      rw [Nat.succ_mul]
      calc
        lower ^ (repetitions + 1) =
            lower * lower ^ repetitions := by rw [pow_succ']
        _ ≤ lower * remainingMass K (repetitions * block) start :=
          by simpa [mul_comm] using mul_le_mul_left ih lower
        _ ≤ remainingMass K (repetitions * block + block) start :=
          mul_remainingMass_le_remainingMass_add
            K (repetitions * block) block start lower hlower

/-- Repeating a block with a uniform upper survival bound gives the
corresponding power upper bound. -/
theorem remainingMass_mul_le_pow
    (K : Kernel S S) (block repetitions : ℕ) (start : S) (upper : ENNReal)
    (hupper : ∀ state, remainingMass K block state ≤ upper) :
    remainingMass K (repetitions * block) start ≤ upper ^ repetitions := by
  induction repetitions with
  | zero => simp
  | succ repetitions ih =>
      rw [Nat.succ_mul]
      calc
        remainingMass K (repetitions * block + block) start ≤
            upper * remainingMass K (repetitions * block) start :=
          remainingMass_add_le_mul_remainingMass
            K (repetitions * block) block start upper hupper
        _ ≤ upper * upper ^ repetitions := by
          simpa [mul_comm] using mul_le_mul_left ih upper
        _ = upper ^ (repetitions + 1) := by rw [pow_succ']

end ProbabilityTheory.Kernel
