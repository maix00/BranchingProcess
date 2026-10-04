import Analysis.Fourier.PositiveDefinite

open ProbabilityTheory Complex ComplexConjugate

example (φ ψ : ℝ → ℂ) (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (fun x => φ x * ψ x) :=
  hφ.mul hψ

example : IsPositiveDefinite (fun _ : ℝ => (0 : ℂ)) := by
  intro n x c
  simp

example : IsPositiveDefinite (fun _ : ℝ => (2 : ℂ)) := by
  intro n x c
  have hsum :
      ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j =
        ↑(Complex.normSq (∑ i : Fin n, c i)) := by
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hform :
      ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * (2 : ℂ) =
        ↑(2 * Complex.normSq (∑ i : Fin n, c i)) := by
    calc
      _ = (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j) * 2 := by
        simp_rw [Finset.sum_mul]
      _ = _ := by rw [hsum]; push_cast; ring
  rw [hform, Complex.nonneg_iff]
  constructor
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Complex.normSq_nonneg _)
  · simp

example (x : ℝ) :
    IsPositiveDefinite (fun ξ : ℝ => Complex.exp (-(↑x * ↑ξ * I))) :=
  isPositiveDefinite_exp_neg_ofReal_mul x

example (x : ℝ) :
    IsPositiveDefinite (fun ξ : ℝ => Complex.exp (↑x * ↑ξ * I)) :=
  isPositiveDefinite_exp_ofReal_mul x

#print axioms ProbabilityTheory.IsPositiveDefinite.mul
#print axioms ProbabilityTheory.isPositiveDefinite_exp_neg_ofReal_mul
#print axioms ProbabilityTheory.isPositiveDefinite_exp_ofReal_mul
