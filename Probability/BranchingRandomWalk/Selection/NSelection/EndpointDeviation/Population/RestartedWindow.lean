/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder

/-!
# Restarted windows for the positive-a estimate

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveADrift`: for $D=\ell_N-\ell$ and $0\le j\le D$,
  $d_j=(\kappa/c^2)D^{-2/3}j$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveARestartedWindow`: the first stage uses
  $[-b\log N,0]$ before $\ell$ and
  $[-b\log N,(-b+v)\log N]$ at $\ell$; the second stage uses
  $[d_{k-\ell},d_{k-\ell}+cD^{1/3}]$ before $\ell_N$ and
  $[d_D,d_D+vD^{1/3}]$ at $\ell_N$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveAWindowUpper`: the upper endpoint of that window schedule.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.measurableSet_positiveARestartedWindow`: each scheduled window is
  a measurable subset of $\mathbb R$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.positiveARestartedWindow_subset_Iic_upper`: each scheduled window
  is contained in the half-line below its stated upper endpoint.

These are the deterministic window data used in the proof of Proposition 3.1,
equation (4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on
the complete graph*, arXiv:2512.23266 (2025). The directory records their
role in the first stage; the condition $a>0$ remains a parameter of the result.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

/-- Drift of the second-stage tube in the positive-`a` proof of (4.15),
with `κ = π² σ² / 2`. -/
noncomputable def positiveADrift
    (ell ellN : ℕ) (κ c : ℝ) (j : ℕ) : ℝ :=
  κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ ((-2 : ℝ) / 3)) * (j : ℝ)

/-- Restarted path windows for the killed population used in the proof of
(4.15). Up to `ell`, paths remain in `[-b logN, 0]`, with a narrower window
at `ell`. The next stage uses the tilted tube, with a narrower terminal
window at `ellN`. -/
noncomputable def positiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : Set ℝ :=
  if k < ell then Set.Icc (-b * logN) 0
  else if k = ell then Set.Icc (-b * logN) ((-b + v) * logN)
  else if k < ellN then
    Set.Icc (positiveADrift ell ellN κ c (k - ell))
      (positiveADrift ell ellN κ c (k - ell) +
        c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
  else if k = ellN then
    Set.Icc (positiveADrift ell ellN κ c (ellN - ell))
      (positiveADrift ell ellN κ c (ellN - ell) +
        v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
  else ∅

/-- Deterministic upper endpoint for each stage window. -/
noncomputable def positiveAWindowUpper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : ℝ :=
  if k < ell then 0
  else if k = ell then (-b + v) * logN
  else if k < ellN then
    positiveADrift ell ellN κ c (k - ell) +
      c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  else if k = ellN then
    positiveADrift ell ellN κ c (ellN - ell) +
      v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  else 0

theorem measurableSet_positiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    MeasurableSet (positiveARestartedWindow ell ellN logN b v c κ k) := by
  classical
  unfold positiveARestartedWindow
  split_ifs <;> simp [measurableSet_Icc]

theorem positiveARestartedWindow_subset_Iic_upper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    positiveARestartedWindow ell ellN logN b v c κ k ⊆
      Set.Iic (positiveAWindowUpper ell ellN logN b v c κ k) := by
  classical
  unfold positiveARestartedWindow positiveAWindowUpper
  split_ifs <;> simp [Set.Icc_subset_Iic_self]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
