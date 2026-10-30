/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Walk.Speed
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# First-row limits and finite-selection speed

This file transfers almost-sure and `L1` convergence of the first row of a
random array to the pathwise speed of a position sequence identified with its
negative. The limit hypotheses are explicit; callers may obtain them from a
subadditive ergodic theorem or another source.

## Public declarations

- `hasAsymptoticSpeed_of_arrayFirstRowConvergence`: if
  $A_{0,n}(\omega)/n\to c$ almost surely,
  $\left\|A_{0,n}/n-c\right\|_{L^1(\mu)}\to0$, and
  $p_n(\omega)=-A_{0,n}(\omega)$, then
  $p_n(\omega)/n\to -c$ almost surely and
  $\left\|p_n/n+c\right\|_{L^1(\mu)}\to0$.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

/-- If `A 0 n / n` converges almost surely and in `L1` to `c`, and
`p ω n = -A 0 n ω`, then `p ω n / n` has almost-sure speed `-c` and its
normalized position error converges to zero in `L1`. The explicit hypotheses
state exactly the limits used by the translation, without requiring the array
to carry unused subadditivity data. -/
theorem hasAsymptoticSpeed_of_arrayFirstRowConvergence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → ℕ → Ω → ℝ) (c : ℝ) (p : Ω → ℕ → ℝ)
    (hpath : ∀ ω n, p ω n = -A 0 n ω)
    (hA_ae : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * A 0 n ω) atTop (𝓝 c))
    (hA_l1 : Tendsto
      (fun n : ℕ => eLpNorm (fun ω => (n : ℝ)⁻¹ * A 0 n ω - c)
        (1 : ℝ≥0∞) μ) atTop (𝓝 0)) :
    (∀ᵐ ω ∂μ,
      Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
        (𝕜 := ℝ) (p ω) (-c)) ∧
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω => (n : ℝ)⁻¹ * p ω n - (-c)) (1 : ℝ≥0∞) μ)
        atTop (𝓝 0) := by
  constructor
  · filter_upwards [hA_ae] with ω hω
    change Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * p ω n) atTop (𝓝 (-c))
    have hneg : Tendsto
        (fun n : ℕ => -((n : ℝ)⁻¹ * A 0 n ω)) atTop (𝓝 (-c)) := by
      simpa using hω.neg
    apply hneg.congr'
    filter_upwards [] with n
    rw [hpath ω n]
    ring
  · have hnorm : ∀ n : ℕ,
        eLpNorm (fun ω => (n : ℝ)⁻¹ * p ω n - (-c))
          (1 : ℝ≥0∞) μ =
        eLpNorm (fun ω => (n : ℝ)⁻¹ * A 0 n ω - c)
          (1 : ℝ≥0∞) μ := by
      intro n
      have hfun : (fun ω => (n : ℝ)⁻¹ * p ω n - (-c)) =
          fun ω => -((n : ℝ)⁻¹ * A 0 n ω - c) := by
        funext ω
        rw [hpath ω n]
        ring
      rw [hfun]
      change eLpNorm (-(fun ω => (n : ℝ)⁻¹ * A 0 n ω - c))
        (1 : ℝ≥0∞) μ = _
      exact eLpNorm_neg _ _ _
    have hseq : (fun n : ℕ =>
        eLpNorm (fun ω => (n : ℝ)⁻¹ * p ω n - (-c))
          (1 : ℝ≥0∞) μ) =
        fun n : ℕ => eLpNorm (fun ω => (n : ℝ)⁻¹ * A 0 n ω - c)
          (1 : ℝ≥0∞) μ := by
      funext n
      exact hnorm n
    rw [hseq]
    exact hA_l1

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
