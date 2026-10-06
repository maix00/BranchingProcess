/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalGrid.UnitInterval
public import Topology.Cadlag.Skorokhod.Oscillation.Dense
import Topology.Order.UnitInterval.Rational

/-!
# Strict corridors from rational coordinates

A positive uniform margin on rational times, including the terminal time,
extends to every time of a càdlàg path. The margin is essential: rational
pointwise strict inequalities alone do not control an unattained left limit.
-/

@[expose] public section

namespace Skorokhod

open Filter Set
open scoped Topology

/-- A closed spatial interval bound on a dense time set extends to all times
for a càdlàg path when the dense set contains the final time. -/
theorem closedCorridor_on_dense
    {T : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    [DenselyOrdered T] [FirstCountableTopology T] [OrderTop T]
    {D : Set T} (hD : Dense D) (htop : ⊤ ∈ D)
    (path : T → ℝ) (hpath : IsCadlag path) {lower upper : ℝ}
    (hDpath : ∀ t ∈ D, lower ≤ path t ∧ path t ≤ upper) :
    ∀ t, lower ≤ path t ∧ path t ≤ upper := by
  intro t
  by_cases ht : t = ⊤
  · exact ht ▸ hDpath ⊤ htop
  · have httop : t < ⊤ := lt_of_le_of_ne le_top ht
    obtain ⟨u, _, huD, huTendsto⟩ :=
      hD.exists_seq_strictAnti_tendsto_of_lt httop
    have hwithin : Tendsto u atTop (𝓝[Set.Ioi t] t) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨huTendsto, Filter.Eventually.of_forall fun n => (huD n).1.1⟩
    have hvalue : Tendsto (fun n => path (u n)) atTop (𝓝 (path t)) :=
      (hpath.isRightContinuous t).tendsto.comp hwithin
    constructor
    · exact isClosed_Ici.mem_of_tendsto hvalue
        (Filter.Eventually.of_forall fun n => (hDpath (u n) (huD n).2).1)
    · exact isClosed_Iic.mem_of_tendsto hvalue
        (Filter.Eventually.of_forall fun n => (hDpath (u n) (huD n).2).2)

/-- A uniform rational-coordinate corridor, with an explicit positive
margin. -/
def rationalCorridorWithMargin (lower upper : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {f | ∃ margin > 0, ∀ q : RationalGrid.UnitCoordinate,
    lower + margin ≤ f (RationalGrid.unitCoe q) ∧
      f (RationalGrid.unitCoe q) ≤ upper - margin}

/-- Countable-coordinate strict corridor with a rational uniform margin. -/
def rationalCoordinateCorridorWithMargin (lower upper : ℝ) :
    Set (RationalGrid.UnitCoordinate → ℝ) :=
  {x | ∃ margin : ℚ, 0 < (margin : ℝ) ∧
    ∀ q : RationalGrid.UnitCoordinate,
      lower + margin ≤ x q ∧ x q ≤ upper - margin}

/-- A real-margin formulation of the same coordinate event. It is useful
for positive scalar changes, while the rational-margin formulation exposes
countable measurability. -/
def rationalCoordinateCorridorWithRealMargin (lower upper : ℝ) :
    Set (RationalGrid.UnitCoordinate → ℝ) :=
  {x | ∃ margin : ℝ, 0 < margin ∧
    ∀ q : RationalGrid.UnitCoordinate,
      lower + margin ≤ x q ∧ x q ≤ upper - margin}

theorem rationalCoordinateCorridorWithMargin_eq_real
    (lower upper : ℝ) :
    rationalCoordinateCorridorWithMargin lower upper =
      rationalCoordinateCorridorWithRealMargin lower upper := by
  ext x
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    exact ⟨margin, hmargin, hbound⟩
  · rintro ⟨margin, hmargin, hbound⟩
    obtain ⟨q, hqpos, hqmargin⟩ := exists_rat_btwn hmargin
    refine ⟨q, hqpos, ?_⟩
    intro t
    have ht := hbound t
    constructor <;> linarith

/-- Positive scalar multiplication transports a countable-coordinate
uniform corridor, including its positive margin. -/
theorem mem_rationalCoordinateCorridorWithMargin_smul_iff
    (c : ℝ) (hc : 0 < c) (x : RationalGrid.UnitCoordinate → ℝ)
    (lower upper : ℝ) :
    (fun q => c * x q) ∈ rationalCoordinateCorridorWithMargin lower upper ↔
      x ∈ rationalCoordinateCorridorWithMargin (lower / c) (upper / c) := by
  rw [rationalCoordinateCorridorWithMargin_eq_real,
    rationalCoordinateCorridorWithMargin_eq_real]
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
      {x : RationalGrid.UnitCoordinate → ℝ |
        ∀ q, lower + (margin : ℝ) ≤ x q ∧
          x q ≤ upper - (margin : ℝ)} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun q =>
      (measurableSet_le measurable_const (measurable_pi_apply q)).inter
        (measurableSet_le (measurable_pi_apply q) measurable_const)
  rw [show rationalCoordinateCorridorWithMargin lower upper =
      ⋃ margin : ℚ,
        if 0 < (margin : ℝ) then
          {x : RationalGrid.UnitCoordinate → ℝ |
            ∀ q, lower + (margin : ℝ) ≤ x q ∧
              x q ≤ upper - (margin : ℝ)}
        else ∅ by
      ext x
      simp [rationalCoordinateCorridorWithMargin]]
  exact MeasurableSet.iUnion fun margin => by
    split_ifs
    · exact hmargin margin
    · exact MeasurableSet.empty

/-- A uniform rational corridor with a terminal endpoint window. -/
def rationalCoordinateCorridorReturnWithMargin
    (lower upper coreLower coreUpper : ℝ) :
    Set (RationalGrid.UnitCoordinate → ℝ) :=
  rationalCoordinateCorridorWithMargin lower upper ∩
    {x | x ⊤ ∈ Set.Ioo coreLower coreUpper}

theorem mem_rationalCoordinateCorridorReturnWithMargin_smul_iff
    (c : ℝ) (hc : 0 < c) (x : RationalGrid.UnitCoordinate → ℝ)
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
    Set (RationalGrid.UnitCoordinate → ℝ) :=
  rationalCoordinateCorridorWithMargin lower upper ∩
    {x | x ⊤ ∈ Set.Ioc coreLower coreUpper}

/-- Positive scaling transports both the corridor margin and the
left-open, right-closed terminal window. -/
theorem mem_rationalCoordinateCorridorIocReturnWithMargin_smul_iff
    (c : ℝ) (hc : 0 < c) (x : RationalGrid.UnitCoordinate → ℝ)
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

/-- Rational and full-path positive-margin corridor events coincide. -/
theorem rationalCorridorWithMargin_eq (lower upper : ℝ) :
    rationalCorridorWithMargin lower upper = rangeInOpenInterval lower upper := by
  have hD : Dense (Set.range RationalGrid.unitCoe) :=
    RationalGrid.denseRange_unitCoe
  have htop : (⊤ : unitInterval) ∈ Set.range RationalGrid.unitCoe := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    apply Subtype.ext
    simp [RationalGrid.unitCoe]
  ext f
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    refine ⟨margin, hmargin, ?_⟩
    apply closedCorridor_on_dense hD htop f f.isCadlag_toFun
    intro t ht
    obtain ⟨q, rfl⟩ := ht
    exact hbound q
  · rintro ⟨margin, hmargin, hbound⟩
    exact ⟨margin, hmargin, fun q => hbound _⟩

/-- On càdlàg paths, the countable-coordinate event is exactly the full
strict corridor event. -/
theorem mem_rationalCoordinateCorridorWithMargin_iff
    (f : CadlagPath unitInterval ℝ) (lower upper : ℝ) :
    (fun q => f (RationalGrid.unitCoe q)) ∈
        rationalCoordinateCorridorWithMargin lower upper ↔
      f ∈ rangeInOpenInterval lower upper := by
  rw [← rationalCorridorWithMargin_eq]
  constructor
  · rintro ⟨margin, hmargin, hbound⟩
    exact ⟨(margin : ℝ), hmargin, hbound⟩
  · rintro ⟨margin, hmargin, hbound⟩
    obtain ⟨q, hq0, hqmargin⟩ := exists_rat_btwn hmargin
    refine ⟨q, hq0, ?_⟩
    intro t
    have ht := hbound t
    constructor <;> linarith

end Skorokhod

end
