import Mathlib.Probability.Distributions.Bernoulli

/-!
# The Rademacher distribution

The Rademacher law is the equal mixture of the point masses at `-1` and `1`.
It is defined as a specialization of mathlib's `bernoulliMeasure`.
-/

open MeasureTheory unitInterval

namespace ProbabilityTheory

/-- The probability measure assigning mass `1 / 2` to each of `-1` and `1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  Ber((-1 : ℝ), 1, ⟨1 / 2, by constructor <;> norm_num⟩)

noncomputable instance rademacherMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- Encode the two Rademacher increments by a Boolean branch. -/
def rademacherOfBool (step : Bool) : ℝ :=
  if step then 1 else -1

theorem measurable_rademacherOfBool : Measurable rademacherOfBool :=
  measurable_of_countable _

/-- The fair Bernoulli law on the two Boolean branches. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  Ber(false, true, ⟨1 / 2, by constructor <;> norm_num⟩)

noncomputable instance fairBoolMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure fairBoolMeasure := by
  unfold fairBoolMeasure
  infer_instance

@[simp] theorem fairBoolMeasure_singleton (step : Bool) :
    fairBoolMeasure {step} = ENNReal.ofReal (1 / 2 : ℝ) := by
  cases step <;> simp [fairBoolMeasure]
  all_goals
    rw [ENNReal.coe_nnreal_eq]
    simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num

/-- The fair Boolean Bernoulli law pushes forward to the Rademacher law. -/
theorem map_fairBernoulli_rademacherOfBool :
    fairBoolMeasure.map rademacherOfBool = rademacherMeasure := by
  unfold fairBoolMeasure
  rw [map_bernoulliMeasure]
  rfl

/-- Integration against the Rademacher law is symmetric averaging. -/
theorem integral_rademacherMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂rademacherMeasure = (f (-1) + f 1) / 2 := by
  rw [rademacherMeasure, integral_bernoulliMeasure]
  norm_num [smul_eq_mul]
  ring

end ProbabilityTheory
