import Probability.Distributions.Stable.LevyKhintchine

/-!
# Scaling of the stable characteristic exponent

The integer scaling identity follows directly from the stable convolution
semigroup and uniqueness of a continuous logarithm. It is a first step toward
identifying the Lévy measure of a strictly stable law.
-/

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure

/-- At integer scale the Lévy–Khintchine exponent of a strictly stable law
is homogeneous with exponent `α`. -/
theorem IsStrictlyAlphaStable.exponent_nat
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (n : ℕ) (ξ : ℝ) :
    T.exponent ((n : ℝ) ^ (1 / α) * ξ) =
      (n : ℂ) * T.exponent ξ := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  let r : ℝ := (n : ℝ) ^ (1 / α)
  have heq : (fun x : ℝ => T.exponent (r * x)) =
      (fun x : ℝ => (n : ℂ) * T.exponent x) := by
    apply eq_of_cexp_eq_of_continuous
    · exact T.exponent_continuous.comp (continuous_const.mul continuous_id)
    · exact continuous_const.mul T.exponent_continuous
    · simp
    · intro x
      calc
        Complex.exp (T.exponent (r * x)) = charFun μ (r * x) := (hT _).symm
        _ = charFun (stableTimeLaw α μ n) x := by
          rw [stableTimeLaw, charFun_map_mul]
        _ = charFun (μ.iteratedConv n) x := by
          rw [h.stableTimeLaw_nat, Measure.convPower_eq_iteratedConv]
        _ = (charFun μ x) ^ n := Measure.charFun_iteratedConv μ n x
        _ = Complex.exp ((n : ℂ) * T.exponent x) := by
          rw [hT, Complex.exp_nat_mul]
  exact congrFun heq ξ

/-- The exponent satisfies the functional equation encoded by strict
stability, without choosing a closed form for the Lévy measure. -/
theorem IsStrictlyAlphaStable.exponent_scaled_add
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ξ : ℝ) :
    T.exponent (a * ξ) + T.exponent (b * ξ) =
      T.exponent (alphaStableScale α a b * ξ) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have heq : (fun x : ℝ => T.exponent (a * x) + T.exponent (b * x)) =
      (fun x : ℝ => T.exponent (alphaStableScale α a b * x)) := by
    apply eq_of_cexp_eq_of_continuous
    · exact (T.exponent_continuous.comp (continuous_const.mul continuous_id)).add
        (T.exponent_continuous.comp (continuous_const.mul continuous_id))
    · exact T.exponent_continuous.comp (continuous_const.mul continuous_id)
    · simp
    · intro x
      rw [Complex.exp_add, ← hT, ← hT]
      rw [← charFun_map_mul a x, ← charFun_map_mul b x]
      rw [← charFun_conv]
      rw [h.conv_scaled ha hb, charFun_map_mul, hT]
  exact congrFun heq ξ

end ProbabilityTheory
