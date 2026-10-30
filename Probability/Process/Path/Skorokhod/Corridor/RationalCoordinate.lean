/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Topology.Cadlag.Skorokhod.Corridor.Dense

/-!
# Rational-coordinate corridor events

## Public declarations

- `ProbabilityTheory.rationalCoordinateCorridor lower upper` is the set of
  rational-coordinate paths whose values lie in `(lower, upper)` at every
  rational unit time.
- `ProbabilityTheory.measurableSet_rationalCoordinateCorridor lower upper`
  proves that this set is measurable.
- `ProbabilityTheory.rationalCoordinateCorridorReturn lower upper coreLower coreUpper`
  adds the endpoint condition `x(1) ∈ (coreLower, coreUpper)`.
- `ProbabilityTheory.measurableSet_rationalCoordinateCorridorReturn` proves
  measurability of the corridor-and-return set.
- `ProbabilityTheory.rationalCoordinateCorridorReturn_subset_withMargin_enlarged`
  embeds this event into a uniformly margined corridor enlarged by any
  `extra > 0`.
- `ProbabilityTheory.mem_rationalCoordinateCorridorReturn_smul_iff` states
  the exact positive-scaling law for the path corridor and endpoint window.
- `ProbabilityTheory.rationalCoordinateCorridorReturn_mono` proves monotonicity
  under inclusion of both spatial intervals.
-/

@[expose] public section

namespace ProbabilityTheory

/-- A spatial corridor for a path on rational unit time. -/
def rationalCoordinateCorridor (lower upper : ℝ) :
    Set (↑RationalCoordinate.UnitInterval → ℝ) :=
  ⋂ q : ↑RationalCoordinate.UnitInterval,
    {x | x q ∈ Set.Ioo lower upper}

theorem measurableSet_rationalCoordinateCorridor (lower upper : ℝ) :
    MeasurableSet (rationalCoordinateCorridor lower upper) := by
  unfold rationalCoordinateCorridor
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_Ioo.preimage (measurable_pi_apply q)

/-- A block corridor together with a return window for its endpoint. -/
def rationalCoordinateCorridorReturn
    (lower upper coreLower coreUpper : ℝ) :
    Set (↑RationalCoordinate.UnitInterval → ℝ) :=
  rationalCoordinateCorridor lower upper ∩
    {x | x ⊤ ∈ Set.Ioo coreLower coreUpper}

theorem measurableSet_rationalCoordinateCorridorReturn
    (lower upper coreLower coreUpper : ℝ) :
    MeasurableSet
      (rationalCoordinateCorridorReturn lower upper coreLower coreUpper) := by
  exact (measurableSet_rationalCoordinateCorridor lower upper).inter
    (measurableSet_Ioo.preimage (measurable_pi_apply ⊤))

/-- Pointwise strict rational bounds in a smaller corridor supply a uniform
rational margin in any strictly enlarged corridor. -/
theorem rationalCoordinateCorridorReturn_subset_withMargin_enlarged
    (lower upper coreLower coreUpper extra : ℝ) (hextra : 0 < extra) :
    rationalCoordinateCorridorReturn lower upper coreLower coreUpper ⊆
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        (lower - extra) (upper + extra) coreLower coreUpper := by
  intro x hx
  obtain ⟨q, hqpos, hqextra⟩ := exists_rat_btwn hextra
  change x ∈ rationalCoordinateCorridor lower upper ∧
    x ⊤ ∈ Set.Ioo coreLower coreUpper at hx
  refine ⟨⟨q, hqpos, ?_⟩, hx.2⟩
  intro t
  have ht := Set.mem_iInter.mp hx.1 t
  change lower < x t ∧ x t < upper at ht
  constructor <;> linarith

/-- Multiplying a rational path by a positive scalar scales both its
spatial corridor and its endpoint return window. -/
theorem mem_rationalCoordinateCorridorReturn_smul_iff
    (c : ℝ) (hc : 0 < c)
    (x : ↑RationalCoordinate.UnitInterval → ℝ)
    (lower upper coreLower coreUpper : ℝ) :
    (fun q => c * x q) ∈
        rationalCoordinateCorridorReturn lower upper coreLower coreUpper ↔
      x ∈ rationalCoordinateCorridorReturn
        (lower / c) (upper / c) (coreLower / c) (coreUpper / c) := by
  simp only [rationalCoordinateCorridorReturn, rationalCoordinateCorridor,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · intro hx
    constructor
    · intro q
      exact ⟨(div_lt_iff₀ hc).2 (by simpa [mul_comm] using (hx.1 q).1),
        (lt_div_iff₀ hc).2 (by simpa [mul_comm] using (hx.1 q).2)⟩
    · exact ⟨(div_lt_iff₀ hc).2 (by simpa [mul_comm] using hx.2.1),
        (lt_div_iff₀ hc).2 (by simpa [mul_comm] using hx.2.2)⟩
  · intro hx
    constructor
    · intro q
      exact ⟨(by simpa [mul_comm] using (div_lt_iff₀ hc).1 (hx.1 q).1),
        (by simpa [mul_comm] using (lt_div_iff₀ hc).1 (hx.1 q).2)⟩
    · exact ⟨(by simpa [mul_comm] using (div_lt_iff₀ hc).1 hx.2.1),
        (by simpa [mul_comm] using (lt_div_iff₀ hc).1 hx.2.2)⟩

/-- Narrowing both the path corridor and its endpoint return window narrows
the corresponding path event. -/
theorem rationalCoordinateCorridorReturn_mono
    {lower₁ upper₁ coreLower₁ coreUpper₁
      lower₂ upper₂ coreLower₂ coreUpper₂ : ℝ}
    (hlower : lower₂ ≤ lower₁) (hupper : upper₁ ≤ upper₂)
    (hcoreLower : coreLower₂ ≤ coreLower₁)
    (hcoreUpper : coreUpper₁ ≤ coreUpper₂) :
    rationalCoordinateCorridorReturn lower₁ upper₁ coreLower₁ coreUpper₁ ⊆
      rationalCoordinateCorridorReturn lower₂ upper₂ coreLower₂ coreUpper₂ := by
  intro x hx
  simp only [rationalCoordinateCorridorReturn, rationalCoordinateCorridor,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Ioo] at hx ⊢
  refine ⟨?_, ?_⟩
  · intro q
    have hq := hx.1 q
    exact ⟨lt_of_le_of_lt hlower hq.1, lt_of_lt_of_le hq.2 hupper⟩
  · exact ⟨lt_of_le_of_lt hcoreLower hx.2.1,
      lt_of_lt_of_le hx.2.2 hcoreUpper⟩

end ProbabilityTheory
