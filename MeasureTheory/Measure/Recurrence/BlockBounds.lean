/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Basic.ENNReal.Basic

/-!
# Finite-step measure recurrences

This module iterates a uniform multiplicative lower bound for the measures of
a sequence of measurable sets. It does not use a process or filtration.
-/

@[expose] public section

namespace MeasureTheory

open MeasureTheory

/-- A uniform multiplicative lower recurrence iterates to a power lower
bound. -/
theorem pow_le_measure_of_mul_le_succ
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (blocks : ℕ) (c : ENNReal)
    (hzero : 1 ≤ P (E 0))
    (hstep : ∀ j < blocks, c * P (E j) ≤ P (E (j + 1))) :
    c ^ blocks ≤ P (E blocks) := by
  have hiter : ∀ m ≤ blocks, c ^ m ≤ P (E m) := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa using hzero
    | succ m ih =>
        intro hm
        have hmlt : m < blocks := by omega
        calc
          c ^ (m + 1) = c * c ^ m := by rw [pow_succ]; ring
          _ ≤ c * P (E m) := by
            simpa only [mul_comm c] using mul_le_mul_left (ih (by omega)) c
          _ ≤ P (E (m + 1)) := hstep m hmlt
  exact hiter blocks le_rfl

end MeasureTheory

end
