/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core

/-!
# Restarted windows for the positive-initial-mass right-tail estimate

The public declarations are:

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveADrift`: for $D=\ell_N-\ell$ and $0\le j\le D$,
  $d_j=(\kappa/c^2)D^{-2/3}j$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveARestartedWindow`: the first stage uses
  $[-b\log N,0]$ before $\ell$ and
  $[-b\log N,(-b+v)\log N]$ at $\ell$; the second stage uses
  $[d_{k-\ell},d_{k-\ell}+cD^{1/3}]$ before $\ell_N$ and
  $[d_D,d_D+vD^{1/3}]$ at $\ell_N$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveAWindowUpper`: the upper endpoint of that window schedule.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measurableSet_rightTailPositiveARestartedWindow`: each scheduled window is
  a measurable subset of $\mathbb R$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveARestartedWindow_subset_Iic_upper`: each scheduled window
  is contained in the half-line below its stated upper endpoint.

These are the deterministic window data used in the proof of Proposition 3.1,
equation (4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on
the complete graph*, arXiv:2512.23266 (2025). The directory records their
role in the first stage; the condition $a>0$ remains a parameter of the result.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

/-- Drift of the second-stage tube in the positive-`a` proof of (4.15),
with `κ = π² σ² / 2`. -/
noncomputable def rightTailPositiveADrift
    (ell ellN : ℕ) (κ c : ℝ) (j : ℕ) : ℝ :=
  κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ ((-2 : ℝ) / 3)) * (j : ℝ)

/-- Restarted path windows for the killed population used in the proof of
(4.15). Up to `ell`, paths remain in `[-b logN, 0]`, with a narrower window
at `ell`. The next stage uses the tilted tube, with a narrower terminal
window at `ellN`. -/
noncomputable def rightTailPositiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : Set ℝ :=
  if k < ell then Set.Icc (-b * logN) 0
  else if k = ell then Set.Icc (-b * logN) ((-b + v) * logN)
  else if k < ellN then
    Set.Icc (rightTailPositiveADrift ell ellN κ c (k - ell))
      (rightTailPositiveADrift ell ellN κ c (k - ell) +
        c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
  else if k = ellN then
    Set.Icc (rightTailPositiveADrift ell ellN κ c (ellN - ell))
      (rightTailPositiveADrift ell ellN κ c (ellN - ell) +
        v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
  else ∅

/-- Deterministic upper endpoint for each stage window. -/
noncomputable def rightTailPositiveAWindowUpper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : ℝ :=
  if k < ell then 0
  else if k = ell then (-b + v) * logN
  else if k < ellN then
    rightTailPositiveADrift ell ellN κ c (k - ell) +
      c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  else if k = ellN then
    rightTailPositiveADrift ell ellN κ c (ellN - ell) +
      v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  else 0

theorem measurableSet_rightTailPositiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    MeasurableSet (rightTailPositiveARestartedWindow ell ellN logN b v c κ k) := by
  classical
  unfold rightTailPositiveARestartedWindow
  split_ifs <;> simp [measurableSet_Icc]

theorem rightTailPositiveARestartedWindow_subset_Iic_upper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    rightTailPositiveARestartedWindow ell ellN logN b v c κ k ⊆
      Set.Iic (rightTailPositiveAWindowUpper ell ellN logN b v c κ k) := by
  classical
  unfold rightTailPositiveARestartedWindow rightTailPositiveAWindowUpper
  split_ifs <;> simp [Set.Icc_subset_Iic_self]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
