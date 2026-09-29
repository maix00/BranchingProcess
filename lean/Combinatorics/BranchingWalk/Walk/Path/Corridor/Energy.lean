import Combinatorics.BranchingWalk.Walk.Path.Corridor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Corridor energy

The integral width functional used by the Mogulskii rate is separated from
the basic corridor predicates.  The latter remain available without measure
integration imports.
-/

open MeasureTheory Set

namespace Combinatorics.Branching.Walk

/-- The width functional `H_α` from the original theorem, restricted to its
basic corridor representation. -/
noncomputable def corridorEnergy (α : ℝ) (lower upper : ℝ → ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, (upper t - lower t) ^ (-α)

/-- A horizontal corridor of width `width` has energy `width⁻ᵅ`. -/
theorem corridorEnergy_const (α lower upper : ℝ) :
    corridorEnergy α (fun _ => lower) (fun _ => upper) =
      (upper - lower) ^ (-α) := by
  simp [corridorEnergy]

/-- Translating both boundaries leaves the corridor energy unchanged. -/
theorem corridorEnergy_add_const (α shift : ℝ) (lower upper : ℝ → ℝ) :
    corridorEnergy α (fun t => shift + lower t)
        (fun t => shift + upper t) =
      corridorEnergy α lower upper := by
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  ring

/-- Widening the boundaries by `ε` adds `2 * ε` to the width, so the energy of
the outer approximation is the integral of the reciprocal power of the widened
width. -/
theorem corridorEnergy_add_sub (α ε : ℝ) (lower upper : ℝ → ℝ) :
    corridorEnergy α (fun t => lower t - ε) (fun t => upper t + ε) =
      ∫ t in Icc (0 : ℝ) 1, (upper t - lower t + 2 * ε) ^ (-α) := by
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  ring

/-- Shrinking the boundaries by `ε` removes `2 * ε` from the width, so the
energy of the inner approximation is the integral of the reciprocal power of
the shrunk width. -/
theorem corridorEnergy_sub_add (α ε : ℝ) (lower upper : ℝ → ℝ) :
    corridorEnergy α (fun t => lower t + ε) (fun t => upper t - ε) =
      ∫ t in Icc (0 : ℝ) 1, (upper t - lower t - 2 * ε) ^ (-α) := by
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  ring

/-/ Scaling both boundaries by `a > 0` scales the corridor energy by `a ^ (−α)`:
the energy of a corridor whose width is multiplied by `a` is the original energy
divided by `a ^ α`. -/
theorem corridorEnergy_const_mul {α a : ℝ} (ha : 0 < a) {lower upper : ℝ → ℝ}
    (hwidth : ∀ t, 0 < upper t - lower t) :
    corridorEnergy α (fun t => a * lower t) (fun t => a * upper t) =
      a ^ (-α) * corridorEnergy α lower upper := by
  rw [corridorEnergy, corridorEnergy, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have hdiff : a * upper t - a * lower t = a * (upper t - lower t) := by ring
  rw [hdiff, Real.mul_rpow (le_of_lt ha) (le_of_lt (hwidth t))]

end Combinatorics.Branching.Walk
