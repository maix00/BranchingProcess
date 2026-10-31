/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Weak convergence of convolution-semigroup members

## Public declarations

- `ProbabilityTheory.ConvolutionSemigroup.tendsto_measure_of_tendsto_exponent`:
  if the characteristic exponents of a sequence of convolution semigroups
  converge pointwise, then their time-$t$ probability measures converge
  weakly for every fixed $t>0$. The characteristic functions satisfy
  \[
    \widehat\mu_{n,t}(\xi)=\exp\bigl(t\psi_n(\xi)\bigr),\qquad
    \psi_n(\xi)\longrightarrow\psi(\xi),
  \]
  so Lévy's continuity theorem gives $\mu_{n,t}\Rightarrow\mu_t$.
-/

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.ConvolutionSemigroup

/-- Pointwise convergence of characteristic exponents implies weak convergence
of every fixed positive-time member of the corresponding convolution
semigroups. -/
theorem tendsto_measure_of_tendsto_exponent
    {S : ℕ → ProbabilityTheory.ConvolutionSemigroup}
    {Slimit : ProbabilityTheory.ConvolutionSemigroup}
    (hexponent : ∀ ξ : ℝ,
      Tendsto (fun n => (S n).exponent ξ) atTop (𝓝 (Slimit.exponent ξ)))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n => (S n).measure ⟨t, ht⟩) atTop
      (𝓝 (Slimit.measure ⟨t, ht⟩)) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro ξ
  change Tendsto
    (fun n => charFun ((S n).measure ⟨t, ht⟩ : Measure ℝ) ξ) atTop
    (𝓝 (charFun (Slimit.measure ⟨t, ht⟩ : Measure ℝ) ξ))
  simp_rw [ConvolutionSemigroup.charFun_eq]
  exact (Complex.continuous_exp.continuousAt.tendsto.comp
    ((hexponent ξ).const_mul (t : ℂ)))

end ProbabilityTheory.ConvolutionSemigroup

end
