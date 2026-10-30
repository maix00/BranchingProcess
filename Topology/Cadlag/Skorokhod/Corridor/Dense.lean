/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Cadlag.Skorokhod.Oscillation.Dense
import Topology.Order.UnitInterval.Rational
import Topology.Cadlag.Range

/-!
# Strict corridors from rational coordinates

## Public declarations

- `Skorokhod.rationalCoordinateCorridorWithMargin`: the countable-coordinate
  corridor event with a positive real uniform margin.
- `Skorokhod.mem_rationalCoordinateCorridorWithMargin_smul_iff`: for `c > 0`,
  `(q ↦ c * x q)` lies in the corridor `(lower, upper)` iff `x` lies in
  `(lower / c, upper / c)`.
- `Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin`: the
  countable-coordinate corridor event is measurable.
- `Skorokhod.rationalCoordinateCorridorReturnWithMargin`: the uniform-margin
  corridor together with an open terminal window.
- `Skorokhod.mem_rationalCoordinateCorridorReturnWithMargin_smul_iff` and
  `Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin`:
  positive scaling transports the corridor and terminal window, and the event
  is measurable.
- `Skorokhod.rationalCoordinateCorridorIocReturnWithMargin`:
  the corridor with a left-open, right-closed terminal window.
- `Skorokhod.mem_rationalCoordinateCorridorIocReturnWithMargin_smul_iff` and
  `Skorokhod.measurableSet_rationalCoordinateCorridorIocReturnWithMargin`:
  positive scaling transports this event and it is measurable.
- `Skorokhod.mem_rationalCoordinateCorridorWithMargin_iff`: restriction of a
  càdlàg path to rational coordinates belongs to the coordinate event iff
  the path belongs to the full corridor.

A positive uniform margin on rational times, including the terminal time,
extends to every time of a càdlàg path. The margin is essential: rational
pointwise strict inequalities alone do not control an unattained left limit.
-/

@[expose] public section

namespace Skorokhod

open Set
open scoped Topology

/-- Countable-coordinate strict corridor with a positive real uniform margin.
The rational time coordinates make the event countably measurable. -/
def rationalCoordinateCorridorWithMargin (lower upper : ℝ) :
    Set (RationalCoordinate.UnitInterval → ℝ) :=
  {x | ∃ margin : ℝ, 0 < margin ∧
    ∀ q : RationalCoordinate.UnitInterval,
      lower + margin ≤ x q ∧ x q ≤ upper - margin}

/-- Positive scalar multiplication transports a countable-coordinate
uniform corridor, including its positive margin. -/
theorem mem_rationalCoordinateCorridorWithMargin_smul_iff
    (c : ℝ) (hc : 0 < c) (x : RationalCoordinate.UnitInterval → ℝ)
    (lower upper : ℝ) :
    (fun q => c * x q) ∈ rationalCoordinateCorridorWithMargin lower upper ↔
      x ∈ rationalCoordinateCorridorWithMargin (lower / c) (upper / c) := by
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    refine ⟨margin / c, div_pos hmargin hc, ?_⟩
    intro q
    have hq := hbound q
    constructor
    · rw [← add_div]
      exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hq.1)
    · rw [← sub_div]
      exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hq.2)
  · rintro ⟨margin, hmargin, hbound⟩
    refine ⟨c * margin, mul_pos hc hmargin, ?_⟩
    intro q
    have hq := hbound q
    constructor
    · calc
        lower + c * margin = c * (lower / c + margin) := by field_simp
        _ ≤ c * x q := mul_le_mul_of_nonneg_left hq.1 hc.le
    · calc
        c * x q ≤ c * (upper / c - margin) :=
          mul_le_mul_of_nonneg_left hq.2 hc.le
        _ = upper - c * margin := by field_simp

theorem measurableSet_rationalCoordinateCorridorWithMargin
    (lower upper : ℝ) :
    MeasurableSet (rationalCoordinateCorridorWithMargin lower upper) := by
  classical
  have hmargin (margin : ℚ) : MeasurableSet
      {x : RationalCoordinate.UnitInterval → ℝ |
        ∀ q, lower + (margin : ℝ) ≤ x q ∧
          x q ≤ upper - (margin : ℝ)} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun q =>
      (measurableSet_le measurable_const (measurable_pi_apply q)).inter
        (measurableSet_le (measurable_pi_apply q) measurable_const)
  have hEq : rationalCoordinateCorridorWithMargin lower upper =
      ⋃ margin : ℚ,
        if 0 < (margin : ℝ) then
          {x : RationalCoordinate.UnitInterval → ℝ |
            ∀ q, lower + (margin : ℝ) ≤ x q ∧
              x q ≤ upper - (margin : ℝ)}
        else ∅ := by
    ext x
    constructor
    · rintro ⟨r, hr, hbound⟩
      obtain ⟨q, hqpos, hqr⟩ := exists_rat_btwn hr
      refine Set.mem_iUnion.2 ⟨q, ?_⟩
      have hqbound : ∀ t, lower + (q : ℝ) ≤ x t ∧
          x t ≤ upper - (q : ℝ) := by
        intro t
        rcases hbound t with ⟨hlower, hupper⟩
        constructor <;> linarith
      simpa [hqpos] using hqbound
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨q, hq⟩
      by_cases hqpos : 0 < (q : ℝ)
      · have hbound : ∀ t, lower + (q : ℝ) ≤ x t ∧
            x t ≤ upper - (q : ℝ) := by
          simpa [hqpos] using hq
        exact ⟨(q : ℝ), hqpos, hbound⟩
      · simp [hqpos] at hq
  rw [hEq]
  exact MeasurableSet.iUnion fun margin => by
    split_ifs
    · exact hmargin margin
    · exact MeasurableSet.empty

/-- A uniform rational corridor with a terminal endpoint window. -/
def rationalCoordinateCorridorReturnWithMargin
    (lower upper coreLower coreUpper : ℝ) :
    Set (RationalCoordinate.UnitInterval → ℝ) :=
  rationalCoordinateCorridorWithMargin lower upper ∩
    {x | x ⊤ ∈ Set.Ioo coreLower coreUpper}

theorem mem_rationalCoordinateCorridorReturnWithMargin_smul_iff
    (c : ℝ) (hc : 0 < c) (x : RationalCoordinate.UnitInterval → ℝ)
    (lower upper coreLower coreUpper : ℝ) :
    (fun q => c * x q) ∈ rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper ↔
      x ∈ rationalCoordinateCorridorReturnWithMargin
        (lower / c) (upper / c) (coreLower / c) (coreUpper / c) := by
  simp only [rationalCoordinateCorridorReturnWithMargin, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_Ioo]
  rw [mem_rationalCoordinateCorridorWithMargin_smul_iff c hc]
  constructor
  · rintro ⟨hpath, hlo, hhi⟩
    exact ⟨hpath,
      (div_lt_iff₀ hc).2 (by simpa [mul_comm] using hlo),
      (lt_div_iff₀ hc).2 (by simpa [mul_comm] using hhi)⟩
  · rintro ⟨hpath, hlo, hhi⟩
    exact ⟨hpath,
      (by simpa [mul_comm] using (div_lt_iff₀ hc).1 hlo),
      (by simpa [mul_comm] using (lt_div_iff₀ hc).1 hhi)⟩

theorem measurableSet_rationalCoordinateCorridorReturnWithMargin
    (lower upper coreLower coreUpper : ℝ) :
    MeasurableSet (rationalCoordinateCorridorReturnWithMargin
      lower upper coreLower coreUpper) :=
  (measurableSet_rationalCoordinateCorridorWithMargin lower upper).inter
    (measurableSet_Ioo.preimage (measurable_pi_apply ⊤))

/-- A uniform rational-coordinate corridor with a left-open,
right-closed terminal window. -/
def rationalCoordinateCorridorIocReturnWithMargin
    (lower upper coreLower coreUpper : ℝ) :
    Set (RationalCoordinate.UnitInterval → ℝ) :=
  rationalCoordinateCorridorWithMargin lower upper ∩
    {x | x ⊤ ∈ Set.Ioc coreLower coreUpper}

/-- Positive scaling transports both the corridor margin and the
left-open, right-closed terminal window. -/
theorem mem_rationalCoordinateCorridorIocReturnWithMargin_smul_iff
    (c : ℝ) (hc : 0 < c) (x : RationalCoordinate.UnitInterval → ℝ)
    (lower upper coreLower coreUpper : ℝ) :
    (fun q => c * x q) ∈
        rationalCoordinateCorridorIocReturnWithMargin
          lower upper coreLower coreUpper ↔
      x ∈ rationalCoordinateCorridorIocReturnWithMargin
        (lower / c) (upper / c) (coreLower / c) (coreUpper / c) := by
  simp only [rationalCoordinateCorridorIocReturnWithMargin,
    Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc]
  rw [mem_rationalCoordinateCorridorWithMargin_smul_iff c hc]
  constructor
  · rintro ⟨hpath, hlo, hhi⟩
    exact ⟨hpath,
      (div_lt_iff₀ hc).2 (by simpa [mul_comm] using hlo),
      (le_div_iff₀ hc).2 (by simpa [mul_comm] using hhi)⟩
  · rintro ⟨hpath, hlo, hhi⟩
    exact ⟨hpath,
      (by simpa [mul_comm] using (div_lt_iff₀ hc).1 hlo),
      (by simpa [mul_comm] using (le_div_iff₀ hc).1 hhi)⟩

/-- The left-open, right-closed rational endpoint condition is measurable. -/
theorem measurableSet_rationalCoordinateCorridorIocReturnWithMargin
    (lower upper coreLower coreUpper : ℝ) :
    MeasurableSet (rationalCoordinateCorridorIocReturnWithMargin
      lower upper coreLower coreUpper) :=
  (measurableSet_rationalCoordinateCorridorWithMargin lower upper).inter
    (measurableSet_Ioc.preimage (measurable_pi_apply ⊤))

/-- On càdlàg paths, the countable-coordinate event is exactly the full
strict corridor event. -/
theorem mem_rationalCoordinateCorridorWithMargin_iff
    (f : CadlagPath unitInterval ℝ) (lower upper : ℝ) :
    (fun q => f (RationalCoordinate.toUnitInterval q)) ∈
        rationalCoordinateCorridorWithMargin lower upper ↔
      f ∈ rangeInOpenInterval lower upper := by
  have hD : Dense (Set.range RationalCoordinate.toUnitInterval) :=
    RationalCoordinate.denseRange_toUnitInterval
  have htop : (⊤ : unitInterval) ∈ Set.range RationalCoordinate.toUnitInterval := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    simp [RationalCoordinate.toUnitInterval]
  change (∃ margin : ℝ, 0 < margin ∧
      ∀ q : RationalCoordinate.UnitInterval,
        lower + margin ≤ f (RationalCoordinate.toUnitInterval q) ∧
          f (RationalCoordinate.toUnitInterval q) ≤ upper - margin) ↔
    ∃ margin : ℝ, 0 < margin ∧
      ∀ t, lower + margin ≤ f t ∧ f t ≤ upper - margin
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    refine ⟨margin, hmargin, fun t => ?_⟩
    have hrange : Set.range f ⊆ Set.Icc (lower + margin) (upper - margin) :=
      IsCadlag.range_subset_of_dense hD htop f.isCadlag_toFun isClosed_Icc
        (fun t ht => by
          obtain ⟨q, rfl⟩ := ht
          exact hbound q)
    exact hrange ⟨t, rfl⟩
  · rintro ⟨margin, hmargin, hbound⟩
    exact ⟨margin, hmargin, fun t => hbound (RationalCoordinate.toUnitInterval t)⟩

end Skorokhod

end
