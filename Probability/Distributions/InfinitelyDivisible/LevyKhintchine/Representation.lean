/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.LevyKhintchine
import MeasureTheory.Measure.CharacteristicFunction.Convolution

/-!
# Lévy–Khintchine representation for infinitely divisible laws on ℝ

## Public declarations

* `levyKhintchine_representation` states that every infinitely divisible probability measure
  `μ` on `ℝ` has a Lévy triple `T = (b, σ², ν)` with
  `charFun μ ξ = exp (i b ξ - σ² ξ² / 2 + ∫ (exp(iξx) - 1 - iξx 1_{|x|<1}) dν(x))`.
* `levyKhintchine_of_cpd` gives the same exponent representation for a continuous, Hermitian,
  conditionally positive-definite function `ψ` with `ψ(0) = 0`.
* `levyKhintchine_converse` constructs, from any `LevyKhintchineTriple T`, an infinitely
  divisible probability measure `μ` satisfying `charFun μ ξ = exp (T.exponent ξ)`.

The convolution-semigroup representation and its proof dependencies are documented in
`Semigroup/LevyKhintchine.lean` and `Lemmas/Representation/`.

The one-dimensional law-level representation, converse, and uniqueness are
the content of Theorem 8.1 in Ken-iti Sato, *Lévy Processes and Infinitely
Divisible Distributions*, Cambridge Studies in Advanced Mathematics 68,
Cambridge University Press, 1999 (ISBN 978-0-521-55302-5). This formalization
uses the open unit-ball cutoff; changing between open and closed cutoff
conventions changes only the drift parameter.

The Schoenberg correspondence used by the converse is described by A. S. Holevo,
“Conditionally Positive Definite Functions in Quantum Probability,” *Proceedings of the
International Congress of Mathematicians* (Berkeley, 1986), vol. 2, pp. 1011–1020,
Introduction, opening paragraph. The proceedings scan is available at
<https://sites.math.rutgers.edu/~zeilberg/akherim/icm1986.pdf>.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

/-! ## Representation from a conditionally positive-definite exponent -/

/-- A continuous, conditionally positive definite function `ψ : ℝ → ℂ` with `ψ(0) = 0`
has the Lévy-Khintchine integral representation.

**Proof:**
1. By Schoenberg, `exp(tψ)` is PD, continuous, with value 1 at 0 for each `t > 0`.
2. By Bochner, there exists probability measure `μ_t` with `charFun(μ_t) = exp(tψ)`.
3. The family `{μ_t}` forms a convolution semigroup (see `convolutionSemigroupOfCPD`).
4. The diagonal extraction yields `(b, σ², ν)` on a single subsequence and
   `psi_decomposition` packages them into the triple. -/
theorem levyKhintchine_of_cpd
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cpd : IsConditionallyPositiveDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) :
    ∃ T : LevyKhintchineTriple, ∀ ξ : ℝ,
      ψ ξ = ↑T.drift * ↑ξ * I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure := by
  set S := convolutionSemigroupOfCPD hψ_cont hψ_zero hψ_cpd hψ_herm
  obtain ⟨b, σ_sq, ν, hν_levy, hψ_eq⟩ := S.psi_decomposition
  exact ⟨⟨b, σ_sq, ν, hν_levy⟩, hψ_eq⟩

/-! ## Assembly: Lévy-Khintchine representation -/

/-- **Lévy-Khintchine representation theorem**: every infinitely
divisible probability measure `μ` on `ℝ` has a characteristic function of the
form `exp(ibξ − σ²ξ²/2 + ∫ f(ξ,x) dν(x))` with `f = exp(ixξ) − 1 − ixξ·1_{|x|<1}`
and `ν` a Lévy measure.

This is the forward direction of Sato, *Lévy Processes and Infinitely
Divisible Distributions*, Theorem 8.1, with the open-unit-ball cutoff.

**Proof outline:**
1. `charFun_ne_zero` — characteristic function never vanishes.
2. `exists_continuous_log` — continuous logarithm `ψ` with `charFun μ = exp ψ`.
3. `isConditionallyPositiveDefinite_log` — `ψ` is CPD.
4. `levyKhintchine_of_cpd` — `ψ` has the integral representation. -/
theorem levyKhintchine_representation
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ∃ T : LevyKhintchineTriple, ∀ ξ : ℝ,
      charFun μ ξ = exp (
        ↑T.drift * ↑ξ * I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure) := by
  -- Note: we route through psi_decomposition on `convolutionSemigroupOfMeasure μ h`
  -- (rather than on the Bochner-built `convolutionSemigroupOfCPD` directly) so that
  -- the t=1 member is literally μ.
  set S := convolutionSemigroupOfMeasure μ h
  obtain ⟨b, σ_sq, ν, hν_levy, hψ_eq⟩ := S.psi_decomposition
  refine ⟨⟨b, σ_sq, ν, hν_levy⟩, fun ξ => ?_⟩
  -- charFun μ ξ = exp((1 : ℂ) * S.exponent ξ) via the t=1 patch.
  have hcharFun_one : (S.measure ⟨1, one_pos⟩ : MeasureTheory.ProbabilityMeasure ℝ) =
      ⟨μ, by infer_instance⟩ := convolutionSemigroupOfMeasure_one μ h
  have hcf : charFun μ ξ = exp ((1 : ℂ) * S.exponent ξ) := by
    have h1 := S.charFun_eq ⟨1, one_pos⟩ ξ
    rw [show ((⟨1, one_pos⟩ : {t : ℝ // 0 < t}).val : ℂ) = (1 : ℂ) from by norm_cast] at h1
    rw [show charFun μ ξ = charFun (S.measure ⟨1, one_pos⟩ : Measure ℝ) ξ from by
      rw [hcharFun_one]
      rfl, h1]
  rw [hcf, one_mul, hψ_eq ξ]

/-! ## Converse: every Lévy-Khintchine triple yields an infinitely divisible law -/

/-- **Converse Lévy-Khintchine theorem**: every Lévy-Khintchine triple `T = (b, σ², ν)`
is realised by an infinitely divisible probability measure `μ` on `ℝ` whose characteristic
function is `exp(ψ_T)`, where `ψ_T = T.exponent`.

This is the converse direction of Sato, *Lévy Processes and Infinitely
Divisible Distributions*, Theorem 8.1, with the open-unit-ball cutoff.

**Proof:** feed `ψ_T` — continuous, conditionally positive definite, `ψ_T(0) = 0`, Hermitian —
to the forward machinery `convolutionSemigroupOfCPD` (Schoenberg + Bochner), obtaining a
convolution semigroup with `charFun(μ_t) = exp(t·ψ_T)`. Take `μ := μ_1`. Infinite divisibility
follows because `μ_{1/n}^{∗n}` has characteristic function `exp(n·(1/n)·ψ_T) = exp(ψ_T)`, so
`μ = μ_{1/n}^{∗n}` by `Measure.ext_of_charFun`. -/
theorem levyKhintchine_converse (T : LevyKhintchineTriple) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ IsInfinitelyDivisible μ ∧
      ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ) := by
  set S := convolutionSemigroupOfCPD T.exponent_continuous T.exponent_zero
    T.exponent_cpd T.exponent_hermitian with hS
  -- Characteristic function of the `t`-member: `charFun(μ_t) = exp(t · ψ_T)`.
  have hcf : ∀ (t : {t : ℝ // 0 < t}) (ξ : ℝ),
      charFun (S.measure t : Measure ℝ) ξ = Complex.exp ((↑t.val : ℂ) * T.exponent ξ) :=
    fun t ξ => S.charFun_eq t ξ
  refine ⟨(S.measure ⟨1, one_pos⟩ : Measure ℝ), inferInstance, ?_, ?_⟩
  · -- Infinite divisibility: `μ = μ_{1/n}^{∗n}`.
    intro n hn
    have hnpos : (0 : ℝ) < 1 / n := div_pos one_pos (Nat.cast_pos.mpr hn)
    refine ⟨(S.measure ⟨1 / n, hnpos⟩ : Measure ℝ), inferInstance, ?_⟩
    apply Measure.ext_of_charFun
    funext ξ
    rw [Measure.charFun_convPower, hcf ⟨1 / n, hnpos⟩ ξ, hcf ⟨1, one_pos⟩ ξ,
      ← Complex.exp_nat_mul]
    congr 1
    have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [one_div, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_one, one_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · -- Characteristic function identity at `t = 1`.
    intro ξ
    rw [hcf ⟨1, one_pos⟩ ξ]
    simp only [Complex.ofReal_one, one_mul]

end ProbabilityTheory
