/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.PointFamily

/-!
# Characteristic function of a compound Poisson piece

This is the Fourier form of the point-family probability-generating formula.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Complex

/-- The sum of displacements in one finite-intensity partition piece has
the compound Poisson characteristic function. -/
theorem IsPoissonPointFamily.charFun_pieceSum
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f) (k : ℕ) (ξ : ℝ) :
    charFun (P.map (pieceSum K X f k)) ξ =
      Complex.exp ((m (prmPiece m k)).toReal *
        ((∫ x, Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I)
            ∂(prmPieceLaw m k)) - 1)) := by
  let w : E → ℂ := fun x => Complex.exp (((ξ * f x : ℝ) : ℂ) * Complex.I)
  have hw : Measurable w := by
    fun_prop
  have hnorm : ∀ x, ‖w x‖ ≤ 1 := by
    intro x
    simpa [w] using (Complex.norm_exp_ofReal_mul_I (ξ * f x)).le
  have hmeas : Measurable (pieceSum K X f k) :=
    measurable_pieceSum (hd.measurable_count k)
      (hd.measurable_point k) hf
  rw [charFun_apply_real, integral_map hmeas.aemeasurable (by fun_prop)]
  have hpoint : ∀ ω,
      Complex.exp ((ξ : ℂ) * (pieceSum K X f k ω : ℂ) * Complex.I) =
        ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    unfold pieceSum
    have harg : (ξ : ℂ) * (↑(∑ n ∈ Finset.range (K k ω), f (X k n ω)) : ℂ) * Complex.I =
        ∑ n ∈ Finset.range (K k ω),
          (((ξ * f (X k n ω) : ℝ) : ℂ) * Complex.I) := by
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [harg, Complex.exp_sum]
  simp_rw [hpoint]
  exact integral_pieceProd_eq_exp hd hw hnorm

end ProbabilityTheory
