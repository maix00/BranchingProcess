/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Speed
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Subadditive limits and finite-selection speed

This file records the interface needed after applying a subadditive ergodic
theorem to a finite-selection model.  It does not prove a Kingman or Liggett
theorem: it translates the almost-sure and `L1` conclusions for the first row
of an array into the repository's pathwise speed definition.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

/-- The first-row conclusions supplied by a subadditive ergodic theorem.

`almostSure` is needed for pathwise speed.  `l1` records the accompanying
`L1` convergence and is preserved by changing the sign of the row.  The array
is otherwise arbitrary here: subadditivity, stationarity, and integrability
are hypotheses of whichever theorem establishes this structure, not of the
deterministic translation below. -/
structure SubadditiveArrayLimitData {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → ℕ → Ω → ℝ) (c : ℝ) : Prop where
  almostSure : ∀ᵐ ω ∂μ,
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * A 0 n ω) atTop (𝓝 c)
  l1 : Tendsto
    (fun n : ℕ => eLpNorm (fun ω => (n : ℝ)⁻¹ * A 0 n ω - c)
      (1 : ℝ≥0∞) μ) atTop (𝓝 0)

/-- Translate a first-row subadditive limit into the asymptotic speed of any
position path identified with the negative first row.  The result includes the
corresponding `L1` convergence of the normalized position error.

The path identity is explicit so this lemma can be applied to a concrete
finite-`N` frontier path without baking a particular branching model into the
subadditive-array interface. -/
theorem hasAsymptoticSpeed_of_subadditiveArrayLimit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → ℕ → Ω → ℝ) (c : ℝ) (p : Ω → ℕ → ℝ)
    (hpath : ∀ ω n, p ω n = -A 0 n ω)
    (hA : SubadditiveArrayLimitData μ A c) :
    (∀ᵐ ω ∂μ,
      Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
        (𝕜 := ℝ) (p ω) (-c)) ∧
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω => (n : ℝ)⁻¹ * p ω n - (-c)) (1 : ℝ≥0∞) μ)
        atTop (𝓝 0) := by
  constructor
  · filter_upwards [hA.almostSure] with ω hω
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
    exact hA.l1

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed
