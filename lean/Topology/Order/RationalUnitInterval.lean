/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Order.Interval.RationalGrid

/-!
# Rational points of the unit interval

This file is the unit-interval adapter for the generic rational-grid API.  It
contains the density statement needed by path-space arguments; the finite
common-grid construction itself lives in `Order.Interval.RationalGrid`.
-/

@[expose] public section

open Set

namespace RationalGrid

/-- The canonical inclusion of rational unit-interval points into the real
unit interval. -/
def unitCoe (q : RationalUnitInterval) : unitInterval :=
  ⟨(q : ℚ), by
    constructor
    · exact_mod_cast q.property.1
    · exact_mod_cast q.property.2⟩

theorem injective_unitCoe :
    Function.Injective unitCoe := by
  intro p q hpq
  apply Subtype.ext
  exact Rat.cast_injective (congrArg Subtype.val hpq)

theorem denseRange_unitCoe :
    DenseRange unitCoe := by
  rw [Metric.denseRange_iff]
  intro x radius hradius
  by_cases hx0 : (x : ℝ) = 0
  · refine ⟨⟨0, by simp⟩, ?_⟩
    rw [Subtype.dist_eq]
    simp [unitCoe, hx0, hradius]
  by_cases hx1 : (x : ℝ) = 1
  · refine ⟨⟨1, by simp⟩, ?_⟩
    rw [Subtype.dist_eq]
    simp [unitCoe, hx1, hradius]
  have hx0lt : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx0)
  have hx1lt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hx1
  let lower : ℝ := max 0 ((x : ℝ) - radius)
  let upper : ℝ := min 1 ((x : ℝ) + radius)
  have hlower : lower < (x : ℝ) := by
    dsimp only [lower]
    exact max_lt hx0lt (sub_lt_self _ hradius)
  have hupper : (x : ℝ) < upper := by
    dsimp only [upper]
    exact lt_min hx1lt (lt_add_of_pos_right _ hradius)
  obtain ⟨q, hlq, hqu⟩ := exists_rat_btwn (hlower.trans hupper)
  have hqmem : q ∈ Set.Icc (0 : ℚ) 1 := by
    constructor
    · exact_mod_cast (le_max_left 0 ((x : ℝ) - radius) |>.trans_lt hlq).le
    · exact_mod_cast (hqu.trans_le (min_le_left 1 ((x : ℝ) + radius))).le
  refine ⟨⟨q, hqmem⟩, ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq]
  apply abs_lt.2
  constructor
  · have := hqu.trans_le (min_le_right 1 ((x : ℝ) + radius))
    dsimp only [unitCoe]
    linarith
  · have := (le_max_right 0 ((x : ℝ) - radius)).trans_lt hlq
    dsimp only [unitCoe]
    linarith

end RationalGrid
