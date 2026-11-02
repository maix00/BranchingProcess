/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

public import Probability.Ergodic.Kingman.Basic
import all Probability.Ergodic.Kingman.Lemmas.Derriennic

/-!
# Derriennic's maximal inequalities for subadditive cocycles

## Public declarations

* `ProbabilityTheory.Kingman.limsup_setIntegral_div_nonpos`: if `T` preserves a finite measure and
  `B` is measurable and `T`-invariant, while a.e. on `B` some `g (k+1)` is negative, then
  `limsupₙ ↑((∫_B g (n+1) dμ)/(n+1)) ≤ 0`.
* `ProbabilityTheory.Kingman.setIntegral_div_le_level`: if a.e. on `B` some `a (k+1)` is less
  than `(k+1)β`, then `limsupₙ ↑((∫_B a (n+1) dμ)/(n+1)) ≤ ↑(β (μ B).toReal)`.

These are Karlsson's presentation of Derriennic's Lemma 3.4 and Proposition 3.5 in Anders Karlsson,
“A Proof of the Subadditive Ergodic Theorem,” Chapter 12 of *Groups, Graphs and Random Walks*,
London Mathematical Society Lecture Note Series 436, Cambridge University Press (2017), pp. 343–354,
DOI 10.1017/9781316576571.014. The long leader-sum and integral proof chain is in the adjacent
`Lemmas/` directory.

For an invariant measurable set `B`, the two level hypotheses control the
normalized integrals over `B` by

\[\begin{aligned}
\mu\text{-a.e. }x\in B,\ \exists k,\ g_{k+1}(x)<0
&\Longrightarrow\limsup_{n\to\infty}\uparrow\!\left(
  \frac{1}{n+1}\int_B g_{n+1}\,d\mu\right)\le0,\\
\mu\text{-a.e. }x\in B,\ \exists k,\ a_{k+1}(x)<(k+1)\beta
&\Longrightarrow\limsup_{n\to\infty}\uparrow\!\left(
  \frac{1}{n+1}\int_B a_{n+1}\,d\mu
  \right)\le\uparrow\!\left(\beta\,\operatorname{toReal}(\mu(B))\right).
\end{aligned}\]
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **Derriennic's maximal inequality** (Karlsson, Chapter 12, Lemma 3.4). For a measurable
`T`-invariant set `B` such that a.e. `x ∈ B` has some `k` with `g (k+1) x < 0`,
`limsupₙ ↑((∫_B g (n+1) dμ)/(n+1)) ≤ 0`. -/
theorem limsup_setIntegral_div_nonpos [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    {B : Set X} (hB : MeasurableSet B) (hBinv : T ⁻¹' B = B)
    (hBneg : ∀ᵐ x ∂μ, x ∈ B → ∃ k, g (k + 1) x < 0) :
    Filter.limsup
      (fun n : ℕ => (((∫ x in B, g (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop ≤ 0 :=
  limsup_setIntegral_div_nonpos_aux hT hsub hint hB hBinv hBneg

/-- **Level form of the maximal inequality** (Karlsson, Chapter 12, Proposition 3.5). For a
measurable `T`-invariant set `B` such that a.e. `x ∈ B` has some `k` with
`a (k+1) x < (k+1)β`, `limsupₙ ↑((∫_B a (n+1) dμ)/(n+1)) ≤ ↑(β (μ B).toReal)`. -/
theorem setIntegral_div_le_level [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {a : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T a) (hint : ∀ n, Integrable (a n) μ)
    {B : Set X} (hB : MeasurableSet B) (hBinv : T ⁻¹' B = B) (β : ℝ)
    (hBneg : ∀ᵐ x ∂μ, x ∈ B → ∃ k, a (k + 1) x < (k + 1) * β) :
    Filter.limsup
      (fun n : ℕ => (((∫ x in B, a (n + 1) x ∂μ) / (n + 1) : ℝ) : EReal)) atTop
      ≤ ((β * (μ B).toReal : ℝ) : EReal) :=
  setIntegral_div_le_level_aux hT hsub hint hB hBinv β hBneg

end ProbabilityTheory.Kingman
