/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Order.SetDissipate

/-!
# Congruence for dissipated sets

## Public declarations

For any index type with $\leq$, if $s_y=t_y$ for every $y\leq x$, then
$\operatorname{dissipate}(s,x)=\operatorname{dissipate}(t,x)$.

- `dissipate_congr`: if two set-valued functions agree on the lower interval
  $\{y:y\leq x\}$, their dissipated sets at $x$ agree.

This is a finite-prefix congruence property of `Set.dissipate`; it is
independent of measure and capacity theory.
-/

@[expose] public section

namespace Set

/-- Set-valued functions that agree below `x` have the same dissipate at `x`. -/
theorem dissipate_congr {α β : Type*} [LE α] {s t : α → Set β} {x : α}
    (h_eq : ∀ y ≤ x, s y = t y) :
    Set.dissipate s x = Set.dissipate t x := by
  simp only [Set.dissipate_def]
  congr with m x
  simp only [Set.mem_iInter]
  refine ⟨fun h h_le ↦ ?_, fun h h_le ↦ ?_⟩
    <;> specialize h h_le
  · rwa [h_eq m h_le] at h
  · rwa [h_eq m h_le]

end Set

end
