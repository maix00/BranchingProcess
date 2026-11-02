/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Probability.Distributions.InfinitelyDivisible.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Integrand
public import MeasureTheory.Measure.Levy.Basic
public import Analysis.Fourier.ConditionallyPositiveDefinite.Basic

/-!
# Lévy-Khintchine Data

The **Lévy-Khintchine theorem** characterises infinitely divisible probability measures on `ℝ`:
their characteristic function has the form
`exp(ibξ − σ²ξ²/2 + ∫ (e^{ixξ} − 1 − ixξ·1_{|x|<1}) dν(x))`
where `(b, σ², ν)` is the Lévy-Khintchine triple.

## Public declarations

* `ProbabilityTheory.LevyKhintchineTriple` — the drift, Gaussian variance, and
  Lévy measure data used in the representation theorem; `.levyMeasure_zero` and
  `.lintegral_min_one_sq_lt_top` expose the two measure conditions on its Lévy measure.
* `ProbabilityTheory.LevyKhintchineTriple.exponent` —
  `ψ_T(ξ) = ibξ - σ²ξ²/2 + ∫ (e^{ixξ} - 1 - ixξ·1_{|x|<1}) dν(x)`;
  `.exponent_def` gives its defining equation.
* `.exponent_zero`, `.exponent_continuous`, `.exponent_cpd`, and `.exponent_hermitian` prove
  `ψ_T(0)=0`, continuity, conditional positive definiteness, and
  `ψ_T(-ξ)=conj(ψ_T(ξ))`.

The representation theorem is stated and proved in
`Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Representation`;
uniqueness work is in `Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Uniqueness`.

For a triple `T=(b,\sigma^2,\nu)`, the Lévy-measure conditions and exponent
are

\[\begin{aligned}
\nu(\{0\})&=0,
&\qquad\int^-\min(1,x^2)\,d\nu(x)&<\infty,\\
\psi_T(\xi)
&= ib\xi-\frac{\sigma^2\xi^2}{2}
  +\int\left(e^{ix\xi}-1-ix\xi\mathbf 1_{\{|x|<1\}}\right)\,d\nu(x).
\end{aligned}\]
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- The **Lévy-Khintchine triple** `(b, σ², ν)` consisting of a drift, Gaussian variance,
and Lévy measure. The Lévy measure satisfies `MeasureTheory.IsLevyMeasure`, i.e., `ν({0}) = 0` and
`∫ min(1, x²) dν < ∞`. -/
structure LevyKhintchineTriple where
  /-- Drift parameter. -/
  drift : ℝ
  /-- Gaussian variance (non-negative). -/
  gaussianVariance : ℝ≥0
  /-- Lévy measure satisfying `ν({0}) = 0` and `∫ min(1, x²) dν < ∞`. -/
  levyMeasure : Measure ℝ
  /-- The Lévy measure satisfies the Lévy measure conditions. -/
  isLevyMeasure : MeasureTheory.IsLevyMeasure levyMeasure

namespace LevyKhintchineTriple

variable (T : LevyKhintchineTriple)

theorem levyMeasure_zero : T.levyMeasure {0} = 0 :=
  T.isLevyMeasure.zero_singleton

theorem lintegral_min_one_sq_lt_top :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂T.levyMeasure < ⊤ :=
  T.isLevyMeasure.lintegral_min_one_sq_lt_top

/-- The Lévy–Khintchine exponent of `T`, combining its drift, Gaussian variance,
and compensated jump measure. -/
noncomputable def exponent (T : LevyKhintchineTriple) (ξ : ℝ) : ℂ :=
  ↑T.drift * ↑ξ * Complex.I - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
    + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure

/-- Definitional unfolding of the Lévy–Khintchine exponent. -/
@[simp]
theorem exponent_def (T : LevyKhintchineTriple) (ξ : ℝ) :
    T.exponent ξ = ↑T.drift * ↑ξ * Complex.I - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
      + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure := rfl

/-- The Lévy–Khintchine exponent vanishes at the origin. -/
theorem exponent_zero (T : LevyKhintchineTriple) : T.exponent 0 = 0 := by
  simp [LevyKhintchineTriple.exponent]

end LevyKhintchineTriple

/-- The Lévy-Khintchine exponent is continuous. -/
theorem LevyKhintchineTriple.exponent_continuous (T : LevyKhintchineTriple) :
    Continuous T.exponent := by
  unfold LevyKhintchineTriple.exponent
  have hInt := continuous_integral_levyCompensatedIntegrand T.isLevyMeasure
  fun_prop

/-- The Lévy-Khintchine exponent is conditionally positive definite: the imaginary drift
`ibξ` via `IsConditionallyPositiveDefinite.imaginary_additive`, the Gaussian term `−σ²ξ²/2`
via `IsConditionallyPositiveDefinite.neg_sq` scaled by
`σ²/2 ≥ 0`, and the jump integral via `cpd_integral_levyCompensatedIntegrand`. -/
theorem LevyKhintchineTriple.exponent_cpd (T : LevyKhintchineTriple) :
    IsConditionallyPositiveDefinite T.exponent := by
  have hDrift : IsConditionallyPositiveDefinite
      (fun ξ : ℝ => (T.drift : ℂ) * ↑ξ * I) :=
    IsConditionallyPositiveDefinite.imaginary_additive (AddMonoidHom.id ℝ) T.drift
  have hGauss : IsConditionallyPositiveDefinite
      (fun ξ : ℝ => (↑((T.gaussianVariance : ℝ) / 2) : ℂ) * (-((ξ : ℂ) ^ 2))) :=
    IsConditionallyPositiveDefinite.neg_sq.smul_nonneg
      (show (0 : ℝ) ≤ (T.gaussianVariance : ℝ) / 2 by positivity)
  have hInt := cpd_integral_levyCompensatedIntegrand T.isLevyMeasure
  have key : T.exponent = fun ξ : ℝ =>
      (((T.drift : ℂ) * ↑ξ * I) + (↑((T.gaussianVariance : ℝ) / 2) : ℂ) * (-((↑ξ : ℂ) ^ 2)))
        + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure := by
    funext ξ
    simp only [LevyKhintchineTriple.exponent]
    push_cast
    ring
  rw [key]
  exact IsConditionallyPositiveDefinite.add (G := ℝ)
    (IsConditionallyPositiveDefinite.add (G := ℝ) hDrift hGauss) hInt

/-- The Lévy-Khintchine exponent is Hermitian: `ψ_T(−ξ) = conj(ψ_T(ξ))`. -/
theorem LevyKhintchineTriple.exponent_hermitian (T : LevyKhintchineTriple) (ξ : ℝ) :
    T.exponent (-ξ) = starRingEnd ℂ (T.exponent ξ) := by
  simp only [LevyKhintchineTriple.exponent, map_add, map_sub,
    hermitian_integral_levyCompensatedIntegrand ξ,
    Complex.ofReal_neg, map_mul, map_div₀, map_pow, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring

end ProbabilityTheory
