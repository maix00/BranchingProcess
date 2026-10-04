module

public import Probability.Process.Levy.Jump.Campbell.Integrability

@[expose] public section

/-!
# Integrability under a finite Poisson point configuration

A finite-intensity Poisson measure has finitely many realized atoms almost
surely. Any measurable real test function is therefore integrable against
that realized measure, even when its intensity first moment is infinite.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem integrable_poissonRandomMeasure_of_finite_count
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (ω : Ω) {f : E → ℝ} (hf : Measurable f)
    (hcount : poissonRandomMeasure K X ω Set.univ < ⊤) :
    Integrable f (poissonRandomMeasure K X ω) := by
  have hcountsum : (∑' k, (K k ω : ENNReal)) ≠ ⊤ := by
    have h := poissonRandomMeasure_apply (K := K) (X := X) (ω := ω)
      (A := Set.univ) MeasurableSet.univ
    rw [h] at hcount
    simpa [thinnedCount] using hcount.ne
  have hsupport : {k : ℕ | K k ω ≠ 0}.Finite := by
    have h := ENNReal.finite_const_le_of_tsum_ne_top hcountsum
      (ε := 1) one_ne_zero
    have heq : {k : ℕ | K k ω ≠ 0} =
        {k : ℕ | (1 : ENNReal) ≤ (K k ω : ENNReal)} := by
      ext k
      simp [Nat.one_le_iff_ne_zero]
    rw [heq]
    exact h
  have hnorm : (∫⁻ x, ‖f x‖ₑ ∂(poissonRandomMeasure K X ω)) < ⊤ := by
    rw [lintegral_poissonRandomMeasure (by fun_prop)]
    rw [tsum_eq_sum (s := hsupport.toFinset) (by
      intro k hk
      have hK : K k ω = 0 := by
        by_contra hne
        exact hk (hsupport.mem_toFinset.mpr hne)
      simp [hK])]
    rw [ENNReal.sum_lt_top]
    intro k hk
    rw [ENNReal.sum_lt_top]
    intro j hj
    simp
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact hnorm

theorem IsPoissonPointFamily.ae_integrable_of_finite_intensity
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (hm : m Set.univ < ⊤) :
    ∀ᵐ ω ∂P, Integrable f (poissonRandomMeasure K X ω) := by
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd MeasurableSet.univ hm]
    with ω hω
  exact integrable_poissonRandomMeasure_of_finite_count K X ω hf hω

end ProbabilityTheory
