import Probability.Process.Levy.Jump.Characteristic.Piece

/-!
# Characteristic function of finite Poisson partition sums

The prefix-versus-next-block independence theorem is stronger than pairwise
independence. It lets the single-piece characteristic formula multiply across
any finite prefix of the canonical σ-finite partition.
-/

namespace ProbabilityTheory

open MeasureTheory Complex

/-- Integration over the canonical σ-finite partition recovers the full
intensity integral. -/
theorem hasSum_integral_prmPiece
    {E : Type} [MeasurableSpace E]
    {m : Measure E} [SigmaFinite m]
    {g : E → ℂ} (hg : Integrable g m) :
    HasSum (fun k => ∫ x in prmPiece m k, g x ∂m)
      (∫ x, g x ∂m) := by
  have h := hasSum_integral_iUnion
    (s := prmPiece m) (f := g) (μ := m)
    (fun k => measurableSet_prmPiece)
    pairwise_disjoint_prmPiece (by simpa [iUnion_prmPiece] using hg)
  simpa only [iUnion_prmPiece, setIntegral_univ] using h

/-- A finite-intensity Poisson piece contributes the integral of `w - 1`
against the original intensity. This also covers zero-mass pieces, whose
normalized law is an arbitrary Dirac probability measure. -/
theorem pieceExponent_eq_integral
    {E : Type} [MeasurableSpace E]
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    (k : ℕ) {w : E → ℂ} (hw : Measurable w)
    (hbound : ∀ x, ‖w x‖ ≤ 1) :
    (m (prmPiece m k)).toReal *
      ((∫ x, w x ∂(prmPieceLaw m k)) - 1) =
      ∫ x in prmPiece m k, (w x - 1) ∂m := by
  by_cases hk : m (prmPiece m k) = 0
  · rw [setIntegral_measure_zero _ hk]
    simp [hk]
  · have hInt : Integrable w (prmPieceLaw m k) :=
      (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable
        (Filter.Eventually.of_forall hbound)
    have hsub : (∫ x, w x - 1 ∂(prmPieceLaw m k)) =
        (∫ x, w x ∂(prmPieceLaw m k)) - 1 := by
      rw [integral_sub hInt (integrable_const (1 : ℂ))]
      simp
    have h := integral_smul_prmPieceLaw hk (fun x => w x - 1)
    rw [hsub, Complex.real_smul] at h
    exact h

theorem IsPoissonPointFamily.charFun_prefixPieceSum
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) (ξ : ℝ) :
    charFun (P.map (fun ω =>
      ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)) ξ =
      Complex.exp (∑ k ∈ Finset.range (n + 1),
        (m (prmPiece m k)).toReal *
          ((∫ x, Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I)
              ∂(prmPieceLaw m k)) - 1)) := by
  induction n with
  | zero =>
      simpa only [Nat.zero_add, Finset.range_one, Finset.sum_singleton] using
        hd.charFun_pieceSum hf 0 ξ
  | succ n ih =>
      have hprefix : Measurable (fun ω : Ω =>
          ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) := by
        exact Finset.measurable_sum _ fun k _ =>
          measurable_pieceSum (hd.measurable_count k)
            (hd.measurable_point k) hf
      have hnext : Measurable (pieceSum K X f (n + 1)) :=
        measurable_pieceSum (hd.measurable_count (n + 1))
          (hd.measurable_point (n + 1)) hf
      have hfactor := congrFun
        ((indepFun_pieceSum_prefix_next hd hf n).charFun_map_fun_add_eq_mul
          hprefix.aemeasurable hnext.aemeasurable) ξ
      simp only [Nat.succ_eq_add_one, add_assoc, ← Finset.sum_range_succ] at hfactor ⊢
      rw [hfactor, Pi.mul_apply, ih, hd.charFun_pieceSum hf (n + 1) ξ,
        ← Complex.exp_add, Finset.sum_range_succ]
      congr 1
      simp only [show n + (1 + 1) = (n + 1) + 1 by omega,
        Finset.sum_range_succ]

/-- The finite-prefix formula expressed in the original intensity measure,
with no normalized piece laws in the result. -/
theorem IsPoissonPointFamily.charFun_prefixPieceSum_eq_exp_setIntegrals
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) (ξ : ℝ) :
    charFun (P.map (fun ω =>
      ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)) ξ =
      Complex.exp (∑ k ∈ Finset.range (n + 1),
        ∫ x in prmPiece m k,
          (Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I) - 1) ∂m) := by
  rw [hd.charFun_prefixPieceSum hf n ξ]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  apply pieceExponent_eq_integral k (by fun_prop)
  intro x
  simpa using (Complex.norm_exp_ofReal_mul_I (ξ * f x)).le

end ProbabilityTheory
