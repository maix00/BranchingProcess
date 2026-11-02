/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Integrand
public import MeasureTheory.Measure.Levy.Basic
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.Assembly
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.LargeJumpIdentification

/-!
# Lévy–Khintchine representation for convolution semigroups

## Public declarations

`ConvolutionSemigroup.psi_decomposition` states that every continuous convolution-semigroup
exponent `ψ` has a Lévy–Khintchine representation: there are `b ∈ ℝ`, `σ² ≥ 0`, and a Lévy
measure `ν` such that
`ψ(ξ) = ibξ - σ²ξ²/2 + ∫ (exp(iξx)-1-iξx 1_{|x|<1}) dν(x)` for every `ξ ∈ ℝ`.

The cutoff and subsequence estimates used to prove this result are grouped under
`Lemmas/Representation/`.

Every convolution-semigroup exponent has a Lévy–Khintchine representation
with a Lévy measure:

\[
\psi(\xi)=ib\xi-\frac{\sigma^2\xi^2}{2}
+\int\left(e^{ix\xi}-1-ix\xi\mathbf 1_{\{|x|<1\}}\right)\,d\nu(x),
\qquad \nu(\{0\})=0,\quad
\int^-\min(1,x^2)\,d\nu(x)<\infty.
\]
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory
namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-- **Main assembly.** The characteristic exponent `ψ` of `S` decomposes into the
Lévy-Khintchine triple `(b, σ², ν)` where `ν` is the externally extracted Lévy
measure on `ℝ\{0}`.

The diagonal extraction `exists_drift_variance_jumpMeasure_along_seq` produces all
three witnesses along a single subsequence; the formula then follows from
`psi_eq_levyKhintchine_formula`. -/
theorem psi_decomposition :
    ∃ (b : ℝ) (σ_sq : ℝ≥0) (ν : Measure ℝ),
      MeasureTheory.IsLevyMeasure ν ∧
      ∀ ξ : ℝ,
        S.exponent ξ = ↑b * ↑ξ * I
          - ↑(σ_sq : ℝ) * ↑ξ ^ 2 / 2
          + ∫ x, levyCompensatedIntegrand ξ x ∂ν := by
  obtain ⟨r, b_r, σ_sq_r, ν, hν, t_seq, hr_mem, hν_r, ht_seq, hb, hσ, h_jump⟩ :=
    S.exists_drift_variance_jumpMeasure_along_seq
  -- Corrected witnesses: drift `b' = b_r + ∫_{r≤|x|<1} x dν`, Gaussian variance
  -- `σ_G² = σ_sq_r − ∫_{|x|<r} x² dν` (≥ 0, packaged via `Real.toNNReal`).
  refine ⟨b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν,
    Real.toNNReal ((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν), ν, hν, ?_⟩
  intro ξ
  -- σ_G² ≥ 0, so its `Real.toNNReal` coercion is honest (no truncation).
  have hr_pos : (0 : ℝ) < r := by linarith [hr_mem.1]
  have hnn : (0 : ℝ) ≤ (σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν := by
    have := S.smallBall_second_moment_nu_le hr_pos hν hν_r hσ h_jump
    linarith
  rw [show (↑(Real.toNNReal ((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν)) : ℝ)
        = (σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν from Real.coe_toNNReal _ hnn]
  exact S.psi_eq_levyKhintchine_formula hr_mem b_r σ_sq_r hν hν_r ht_seq hb hσ h_jump ξ

end ConvolutionSemigroup

end ProbabilityTheory
