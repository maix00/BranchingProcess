/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Order.Bounds.Basic

/-!
# Set extrema under order-dual maps

These equivalences express least and greatest elements of images under the
canonical maps between a type and its order dual. Mathlib's duality lemmas in
`Mathlib.Order.Bounds.Basic` assume a preorder; the image formulations here
need only an `LE` relation.

## Public declarations

- `OrderDual.isLeast_image_toDual_iff` states
  $\operatorname{IsLeast}(\operatorname{toDual}(s),\operatorname{toDual}(x))
  \iff \operatorname{IsGreatest}(s,x)$.
- `OrderDual.isGreatest_image_ofDual_iff` states
  $\operatorname{IsGreatest}(\operatorname{ofDual}(s),x)
  \iff \operatorname{IsLeast}(s,\operatorname{toDual}(x))$.
- `OrderDual.isGreatest_image_toDual_iff` states
  $\operatorname{IsGreatest}(\operatorname{toDual}(s),\operatorname{toDual}(x))
  \iff \operatorname{IsLeast}(s,x)$.
-/

@[expose] public section

namespace OrderDual

variable {ι : Type*}

/-- A set has greatest element `x` exactly when its image under `toDual` has
least element `toDual x`. -/
theorem isLeast_image_toDual_iff [LE ι] {s : Set ι} {x : ι} :
    IsLeast (toDual '' s) (toDual x) ↔ IsGreatest s x := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨?_, ?_⟩
    · simpa using hx
    · intro y hy
      exact (toDual_le_toDual).1 (hmin ⟨y, hy, rfl⟩)
  · rintro ⟨hx, hmax⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (toDual_le_toDual).2 (hmax hy)

/-- A set in the dual order has least element `toDual x` exactly when its
image under `ofDual` has greatest element `x`. -/
theorem isGreatest_image_ofDual_iff [LE ι] {s : Set (OrderDual ι)} {x : ι} :
    IsGreatest (ofDual '' s) x ↔ IsLeast s (toDual x) := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨?_, ?_⟩
    · simpa using hx
    · intro z hz
      have h := hmax ⟨z, hz, rfl⟩
      simpa using (toDual_le_toDual (a := x) (b := ofDual z)).2 h
  · rintro ⟨hx, hmin⟩
    refine ⟨⟨toDual x, by simpa using hx, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h := hmin hz
    simpa using (toDual_le_toDual (a := x) (b := ofDual z)).1 h

/-- A set has least element `x` exactly when its image under `toDual` has
greatest element `toDual x`. -/
theorem isGreatest_image_toDual_iff [LE ι] {s : Set ι} {x : ι} :
    IsGreatest (toDual '' s) (toDual x) ↔ IsLeast s x := by
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨?_, ?_⟩
    · simpa using hx
    · intro y hy
      exact (toDual_le_toDual).1 (hmax ⟨y, hy, rfl⟩)
  · rintro ⟨hx, hmin⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (toDual_le_toDual).2 (hmin hy)

end OrderDual

end
