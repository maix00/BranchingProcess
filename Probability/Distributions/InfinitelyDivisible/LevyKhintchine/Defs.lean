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

/-!
# Lévy-Khintchine Data

The **Lévy-Khintchine theorem** characterises infinitely divisible probability measures on `ℝ`:
their characteristic function has the form
`exp(ibξ − σ²ξ²/2 + ∫ (e^{ixξ} − 1 − ixξ·1_{|x|<1}) dν(x))`
where `(b, σ², ν)` is the Lévy-Khintchine triple.

## Main definitions

* `ProbabilityTheory.LevyKhintchineTriple` — the drift, Gaussian variance, and
  Lévy measure data used in the representation theorem.
* `ProbabilityTheory.LevyKhintchineTriple.exponent` —
  `ψ_T(ξ) = ibξ - σ²ξ²/2 + ∫ (e^{ixξ} - 1 - ixξ·1_{|x|<1}) dν(x)`.

The representation theorem is stated and proved in
`Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Representation`;
uniqueness work is in `Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Uniqueness`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
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

end ProbabilityTheory
