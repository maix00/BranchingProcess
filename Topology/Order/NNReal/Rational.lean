/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.NNRat.Encodable
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Nonnegative rational coordinates in the nonnegative reals

## Public declarations

- `NNRat.denseRange_cast_nnreal` states that the canonical inclusion
  $\mathbb Q_{\ge 0}\hookrightarrow\mathbb R_{\ge 0}$ has dense range.
- `NNRat.exists_between_nnreal` places a nonnegative rational strictly
  between any two strictly ordered nonnegative real numbers.

These are order-topological facts independent of stochastic processes. They
provide the countable dense observation set used by continuous-path laws.
-/

@[expose] public section

open scoped NNReal

namespace NNRat

/-- The canonical inclusion of nonnegative rational numbers in the
nonnegative real numbers has dense range. -/
theorem denseRange_cast_nnreal :
    DenseRange (fun q : ℚ≥0 => (q : ℝ≥0)) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  by_cases hx : x = 0
  · subst x
    refine ⟨0, ?_⟩
    rw [NNReal.dist_eq]
    simpa using hε
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

/-- A nonnegative rational lies strictly between any two strictly ordered
nonnegative reals. -/
theorem exists_between_nnreal {a b : ℝ≥0} (hab : a < b) :
    ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b := by
  obtain ⟨q, haq, hqb⟩ :=
    exists_rat_btwn (show (a : ℝ) < b by exact_mod_cast hab)
  have hq : 0 ≤ q := by
    exact_mod_cast (lt_of_le_of_lt a.property haq).le
  refine ⟨⟨q, hq⟩, ?_, ?_⟩
  · exact_mod_cast haq
  · exact_mod_cast hqb

end NNRat

end
