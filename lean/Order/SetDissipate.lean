/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Order.SetDissipate

/-!
# Congruence for dissipated sets

This is a finite-prefix congruence property of `Set.dissipate`; it is
independent of measure and capacity theory.
-/

@[expose] public section

namespace Set

/-- Sequences of sets that agree through index `n` have the same dissipate
at `n`. -/
theorem dissipate_congr {β : Type*} {s t : ℕ → Set β} {n : ℕ}
    (h_eq : ∀ m ≤ n, s m = t m) :
    Set.dissipate s n = Set.dissipate t n := by
  simp only [Set.dissipate_def]
  congr with m x
  simp only [Set.mem_iInter]
  refine ⟨fun h h_le ↦ ?_, fun h h_le ↦ ?_⟩
    <;> specialize h h_le
  · rwa [h_eq m h_le] at h
  · rwa [h_eq m h_le]

end Set

end
