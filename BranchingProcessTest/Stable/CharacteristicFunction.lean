import Probability.Distributions.Stable.CharacteristicFunction

open MeasureTheory ProbabilityTheory

example {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ t : ℝ, ‖charFun μ t‖ = Real.exp (-c * |t| ^ α) :=
  h.exists_pos_norm_charFun_eq_exp

example {μ : Measure ℝ} (h : IsAlphaStable 1 μ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ t : ℝ, ‖charFun μ t‖ = Real.exp (-c * |t|) := by
  obtain ⟨c, hc, hchar⟩ := h.exists_pos_norm_charFun_eq_exp
  refine ⟨c, hc, ?_⟩
  intro t
  simpa using hchar t

#print axioms MeasureTheory.exists_dirac_of_norm_charFun_eq_one
#print axioms ProbabilityTheory.IsAlphaStable.norm_charFun_weightedSum
#print axioms ProbabilityTheory.IsAlphaStable.exists_pos_norm_charFun_eq_exp
