import Probability.Kernel.Survival

/-!
# Blocking bounds for remaining kernel mass

Bounds proved for one fixed block extend to arbitrary elapsed times by using
the quotient and one possible final incomplete block.  This file contains the
order-theoretic part of blocking; no finite-state or random-walk assumptions
are needed.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- A uniform lower bound for one block controls an arbitrary elapsed time,
at the cost of one additional complete block. -/
theorem pow_succ_div_le_remainingMass
    (K : Kernel S S) [IsSubMarkovKernel K]
    {block : ℕ} (hblock : 0 < block) (n : ℕ) (start : S) (lower : ENNReal)
    (hlower : ∀ state, lower ≤ remainingMass K block state) :
    lower ^ (n / block + 1) ≤ remainingMass K n start := by
  have htime : n ≤ (n / block + 1) * block := by
    have hlt : n < (n / block + 1) * block := by
      simpa [mul_comm] using Nat.lt_mul_div_succ n hblock
    exact hlt.le
  calc
    lower ^ (n / block + 1) ≤
        remainingMass K ((n / block + 1) * block) start :=
      pow_le_remainingMass_mul K block (n / block + 1) start lower hlower
    _ ≤ remainingMass K n start := antitone_remainingMass K start htime

/-- A uniform upper bound for one block controls an arbitrary elapsed time
through the number of complete blocks it contains. -/
theorem remainingMass_le_pow_div
    (K : Kernel S S) [IsSubMarkovKernel K]
    (block n : ℕ) (start : S) (upper : ENNReal)
    (hupper : ∀ state, remainingMass K block state ≤ upper) :
    remainingMass K n start ≤ upper ^ (n / block) := by
  have htime : n / block * block ≤ n := Nat.div_mul_le_self n block
  calc
    remainingMass K n start ≤
        remainingMass K (n / block * block) start :=
      antitone_remainingMass K start htime
    _ ≤ upper ^ (n / block) :=
      remainingMass_mul_le_pow K block (n / block) start upper hupper

/-- The two-sided arbitrary-time blocking estimate. -/
theorem remainingMass_bounds_of_block
    (K : Kernel S S) [IsSubMarkovKernel K]
    {block : ℕ} (hblock : 0 < block) (n : ℕ) (start : S)
    (lower upper : ENNReal)
    (hlower : ∀ state, lower ≤ remainingMass K block state)
    (hupper : ∀ state, remainingMass K block state ≤ upper) :
    lower ^ (n / block + 1) ≤ remainingMass K n start ∧
      remainingMass K n start ≤ upper ^ (n / block) :=
  ⟨pow_succ_div_le_remainingMass K hblock n start lower hlower,
    remainingMass_le_pow_div K block n start upper hupper⟩

end ProbabilityTheory.Kernel
