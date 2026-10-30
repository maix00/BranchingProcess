/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Max

/-!
# Translating finite ordered ranges into a standard interval

Let $G$ be a linearly ordered additive group, let $\iota$ be an index type,
let $s\subseteq\iota$ be nonempty and finite, let $x:\iota\to G$, and let
$w\in G$. If
$|x_i-x_j|\le w$ for every $i,j\in s$, translating each value by the negative
of the minimum places the selected family in $[0,w]$:
\[
  \exists c\in G,\quad \forall i\in s,\quad c+x_i\in[0,w].
\]
The statement uses only the finite order structure and applies, in
particular, to integer-valued paths.

Mathlib supplies finite minimum selection and the ordered-group absolute value;
the diameter-to-translation estimate is the additional result proved here.

## Public declarations

- `exists_translate_into_Icc_of_pairwise_dist_le` states that for a
  nonempty finite set $s$, a width $w\in G$, and $x:ι\to G$, if
  $|x_i-x_j|\leq w$ for all $i,j\in s$, then some $c\in G$ satisfies
  $0\leq c+x_i\leq w$ for every $i\in s$.
-/

@[expose] public section

namespace Order.Bounds

/-- A finite nonempty family of bounded diameter can be translated into the
standard interval `[0,width]`. -/
theorem exists_translate_into_Icc_of_pairwise_dist_le
    {ι : Type*} {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] (s : Finset ι) (hs : s.Nonempty) (x : ι → G)
    (width : G) (hosc : ∀ i ∈ s, ∀ j ∈ s, |x i - x j| ≤ width) :
    ∃ translate : G, ∀ i ∈ s,
      translate + x i ∈ Set.Icc (0 : G) width := by
  obtain ⟨imin, himin, hmin⟩ := Finset.exists_min_image s x hs
  let minimum : G := x imin
  have hminimum (i : ι) (hi : i ∈ s) : minimum ≤ x i := by
    exact hmin i hi
  refine ⟨-minimum, ?_⟩
  intro i hi
  have hnonneg : 0 ≤ x i - minimum := sub_nonneg.mpr (hminimum i hi)
  have hosc' := hosc i hi imin himin
  rw [abs_of_nonneg hnonneg] at hosc'
  constructor
  · simpa [minimum, sub_eq_add_neg, add_comm] using hnonneg
  · simpa [minimum, sub_eq_add_neg, add_comm] using hosc'

end Order.Bounds

end
