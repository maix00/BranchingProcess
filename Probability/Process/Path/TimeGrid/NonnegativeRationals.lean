/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.NNRat.Encodable
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Nonnegative rational observation times

The public definition and theorems in this file are:

- `ProbabilityTheory.nonnegativeRationalTime`:
  the inclusion $\mathbb Q_{\ge0}\hookrightarrow\mathbb R_{\ge0}$.
- `ProbabilityTheory.nonnegativeRationalTime_injective`:
  this inclusion is injective.
- `ProbabilityTheory.denseRange_nonnegativeRationalTime`:
  nonnegative rational observation times are dense in the nonnegative
  real time axis.
- `ProbabilityTheory.exists_nonnegativeRationalTime_between`:
  any two strictly ordered nonnegative real times enclose a
  nonnegative rational time.

This dense time set determines continuous-path laws by finite-dimensional
distributions and supports path-level independence arguments.
-/

@[expose] public section

open scoped NNReal

namespace ProbabilityTheory

/-- Include a nonnegative rational time in the nonnegative real axis. -/
def nonnegativeRationalTime (q : ℚ≥0) : ℝ≥0 := q

/-- The inclusion of nonnegative rational times is injective. -/
theorem nonnegativeRationalTime_injective :
    Function.Injective nonnegativeRationalTime :=
  NNRat.cast_injective

/-- Nonnegative rational times are dense in the nonnegative real axis. -/
theorem denseRange_nonnegativeRationalTime :
    DenseRange nonnegativeRationalTime := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_⟩
    rw [NNReal.dist_eq]
    simpa [nonnegativeRationalTime] using hε
  · have hxreal : (x : ℝ) ≠ 0 := by
      intro hx0
      exact hx (NNReal.coe_injective hx0)
    have hxpos : 0 < (x : ℝ) :=
      lt_of_le_of_ne x.2 (Ne.symm hxreal)
    let lower : ℝ := max 0 ((x : ℝ) - ε)
    have hlowerUpper : lower < (x : ℝ) + ε := by
      dsimp [lower]
      exact max_lt (by linarith) (by linarith)
    obtain ⟨q, hlowerq, hqupper⟩ := exists_rat_btwn hlowerUpper
    have hqnonneg : 0 ≤ q := by
      have hqpos := (le_max_left 0 ((x : ℝ) - ε)).trans_lt hlowerq
      exact_mod_cast hqpos.le
    refine ⟨⟨q, hqnonneg⟩, ?_⟩
    rw [NNReal.dist_eq, abs_lt]
    constructor
    · change -ε < (x : ℝ) - (q : ℝ)
      linarith [hqupper]
    · change (x : ℝ) - (q : ℝ) < ε
      have hlow : (x : ℝ) - ε < q :=
        (le_max_right 0 ((x : ℝ) - ε)).trans_lt hlowerq
      linarith

/-- Choose a nonnegative rational time strictly between two
nonnegative real times. -/
theorem exists_nonnegativeRationalTime_between {a b : ℝ≥0} (hab : a < b) :
    ∃ q : ℚ≥0, a < nonnegativeRationalTime q ∧ nonnegativeRationalTime q < b := by
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (show (a : ℝ) < b by exact_mod_cast hab)
  have hq : 0 ≤ q := by
    exact_mod_cast (lt_of_le_of_lt a.property haq).le
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · exact_mod_cast haq
  · exact_mod_cast hqb

end ProbabilityTheory

end
