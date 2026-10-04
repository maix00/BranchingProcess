module

public import Probability.Distributions.InfinitelyDivisible.LevyMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-!
# Scaling Lévy measures

The image of a Lévy measure under a nonzero real dilation is again a Lévy
measure. This is the measure-level input for scaling Lévy–Khintchine triples.
-/

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure ENNReal

private theorem min_one_sq_mul_le (a x : ℝ) :
    min 1 ((a * x) ^ 2) ≤ max 1 (a ^ 2) * min 1 (x ^ 2) := by
  by_cases hx : x ^ 2 ≤ 1
  · rw [min_eq_right hx]
    calc
      min 1 ((a * x) ^ 2) ≤ (a * x) ^ 2 := min_le_right _ _
      _ = a ^ 2 * x ^ 2 := by ring
      _ ≤ max 1 (a ^ 2) * x ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg x)
  · have hx' : 1 ≤ x ^ 2 := le_of_lt (lt_of_not_ge hx)
    rw [min_eq_left hx']
    calc
      min 1 ((a * x) ^ 2) ≤ 1 := min_le_left _ _
      _ ≤ max 1 (a ^ 2) := le_max_left _ _
      _ = max 1 (a ^ 2) * 1 := (mul_one _).symm

/-- A nonzero dilation preserves the Lévy-measure condition. -/
theorem IsLevyMeasure.map_mul {ν : Measure ℝ}
    (hν : IsLevyMeasure ν) {a : ℝ} (ha : a ≠ 0) :
    IsLevyMeasure (ν.map fun x => a * x) := by
  let f : ℝ → ℝ := fun x => a * x
  have hf : Measurable f := by fun_prop
  have hzero : (ν.map f) {0} = 0 := by
    rw [Measure.map_apply hf (measurableSet_singleton 0)]
    have hpre : f ⁻¹' {0} = ({0} : Set ℝ) := by
      ext x
      simp [f, ha]
    rw [hpre, hν.zero_singleton]
  refine ⟨hzero, ?_⟩
  let M : ℝ := max 1 (a ^ 2)
  let g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (min 1 (x ^ 2))
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hbound : ∀ x : ℝ, g (f x) ≤ ENNReal.ofReal M * g x := by
    intro x
    dsimp [g, f, M]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ max 1 (a ^ 2))]
    exact ENNReal.ofReal_le_ofReal (min_one_sq_mul_le a x)
  rw [show (∫⁻ x, g x ∂ν.map f) = ∫⁻ x, g (f x) ∂ν from lintegral_map hg hf]
  calc
    (∫⁻ x, g (f x) ∂ν) ≤ ∫⁻ x, ENNReal.ofReal M * g x ∂ν :=
      lintegral_mono hbound
    _ = ENNReal.ofReal M * ∫⁻ x, g x ∂ν := lintegral_const_mul _ hg
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) hν.lintegral_min_one_sq_lt_top

end ProbabilityTheory
