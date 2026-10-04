/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Oscillation bounds for real-valued paths

The oscillation bound is stated for an arbitrary index type.  It therefore
applies to finite walk segments as well as to continuous-time paths.
-/

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- A real-valued path has oscillation at most `bound` when any two of its
values differ by at most `bound`. -/
def OscillationBounded {Time : Type*} (path : Time → ℝ) (bound : ℝ) : Prop :=
  ∀ s t, |path s - path t| ≤ bound

/-- Increasing the allowed oscillation preserves boundedness. -/
theorem OscillationBounded.mono {Time : Type*} {path : Time → ℝ}
    {bound₁ bound₂ : ℝ} (hbound : bound₁ ≤ bound₂)
    (hpath : OscillationBounded path bound₁) :
    OscillationBounded path bound₂ :=
  fun s t => (hpath s t).trans hbound

/-- Oscillation boundedness is symmetric in its two path indices. -/
theorem OscillationBounded.symm {Time : Type*} {path : Time → ℝ}
    {bound : ℝ} (hpath : OscillationBounded path bound) (s t : Time) :
    |path t - path s| ≤ bound := by
  simpa [abs_sub_comm] using hpath s t

end Combinatorics.Branching.Walk

end
