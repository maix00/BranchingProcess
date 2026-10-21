/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Partition.LowerCores

/-!
# Finite lower-corridor geometry for step boundaries

Let $t_i$ be the common partition knots,
$a_i=L.rightTrace(t_i)$, and $b_i=U.rightTrace(t_i)$. Under
`StartAdmissible U L` and `TraceSeparated U L`, the core data can be chosen
with $c_0=r_0=0$, $r_i<r_{i+1}$, and
$c_i-r_i,c_i+r_i\in\operatorname{selValues}(U,L,t_i)$ at every knot. The
finite cell levels then satisfy
$a_i<\ell_i<c_i-r_i,c_{i+1}-r_{i+1}$ and
$c_i+r_i,c_{i+1}+r_{i+1}<h_i<b_i$.

- `exists_commonPartitionLowerGeometry` chooses this finite geometry.
- `exists_commonPartitionLowerGeometry_small` also ensures $r_i<\eta$ for
  every knot, for any prescribed $\eta>0$.
-/

open MeasureTheory

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- A finite inner strip can be selected on each cell even when one of the
original boundary traces is infinite. Its lower and upper levels lie beyond
both adjacent endpoint cores and strictly inside the incoming traces. -/
private theorem exists_commonPartitionCellInnerBounds
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    ∃ lo hi : ℝ,
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) < lo ∧
      lo < center (commonPartitionCellLeftKnotIndex upper lower i) -
        radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
      lo < center (commonPartitionCellRightKnotIndex upper lower i) -
        radius (commonPartitionCellRightKnotIndex upper lower i) ∧
      center (commonPartitionCellLeftKnotIndex upper lower i) +
        radius (commonPartitionCellLeftKnotIndex upper lower i) < hi ∧
      center (commonPartitionCellRightKnotIndex upper lower i) +
        radius (commonPartitionCellRightKnotIndex upper lower i) < hi ∧
      hi < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
  let i₀ := commonPartitionCellLeftKnotIndex upper lower i
  let i₁ := commonPartitionCellRightKnotIndex upper lower i
  let left := StepBoundary.commonPartitionGrid upper lower i.val
  let right := StepBoundary.commonPartitionGrid upper lower (i.val + 1)
  have htraceLower : lower.leftTrace right = lower.rightTrace left :=
    StepBoundary.leftTrace_eq_rightTrace_on_precedingCommonCell lower upper lower
      (fun q hq => StepBoundary.mem_commonKnots_of_mem_lower upper lower hq) i
  have htraceUpper : upper.leftTrace right = upper.rightTrace left :=
    StepBoundary.leftTrace_eq_rightTrace_on_precedingCommonCell upper upper lower
      (fun q hq => StepBoundary.mem_commonKnots_of_mem_upper upper lower hq) i
  have hlo₀ : lower.rightTrace left < (center i₀ - radius i₀ : EReal) := by
    exact (le_max_right _ _).trans_lt (hcores i₀).1.1
  have hlo₁Left : lower.leftTrace right < (center i₁ - radius i₁ : EReal) := by
    exact (le_max_left _ _).trans_lt (hcores i₁).1.1
  rw [htraceLower] at hlo₁Left
  have hhi₀ : (center i₀ + radius i₀ : EReal) < upper.rightTrace left := by
    exact (lt_of_lt_of_le (hcores i₀).2.2 (min_le_right _ _))
  have hhi₁Left : (center i₁ + radius i₁ : EReal) < upper.leftTrace right := by
    exact (lt_of_lt_of_le (hcores i₁).2.2 (min_le_left _ _))
  rw [htraceUpper] at hhi₁Left
  obtain ⟨lo₀, hlo₀', hcoreLo₀⟩ := EReal.exists_between_coe_real hlo₀
  obtain ⟨lo₁, hlo₁', hcoreLo₁⟩ := EReal.exists_between_coe_real hlo₁Left
  obtain ⟨hi₀, hcoreHi₀, hhi₀'⟩ := EReal.exists_between_coe_real hhi₀
  obtain ⟨hi₁, hcoreHi₁, hhi₁'⟩ := EReal.exists_between_coe_real hhi₁Left
  refine ⟨min lo₀ lo₁, max hi₀ hi₁, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : lo₀ ≤ lo₁
    · rw [min_eq_left h]
      exact hlo₀'
    · rw [min_eq_right (le_of_not_ge h)]
      exact hlo₁'
  · exact (lt_of_le_of_lt (min_le_left _ _)
      (EReal.coe_lt_coe_iff.mp hcoreLo₀))
  · exact (lt_of_le_of_lt (min_le_right _ _)
      (EReal.coe_lt_coe_iff.mp hcoreLo₁))
  · exact (EReal.coe_lt_coe_iff.mp hcoreHi₀).trans_le (le_max_left hi₀ hi₁)
  · exact (EReal.coe_lt_coe_iff.mp hcoreHi₁).trans_le (le_max_right hi₀ hi₁)
  · by_cases h : hi₀ ≤ hi₁
    · rw [max_eq_right h]
      exact hhi₁'
    · rw [max_eq_left (le_of_not_ge h)]
      exact hhi₀'

/-- A finite endpoint-core system and finite inner corridor bounds exist
simultaneously on every cell of a trace-separated step corridor. The core
radii start at zero and increase strictly, which is what makes the
left-open/right-closed return windows concatenate. Infinite boundary traces
are handled by choosing finite intermediate levels. -/
theorem exists_commonPartitionLowerGeometry
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) :
    ∃ center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ,
      ∃ innerLower innerUpper :
        Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ,
      center ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      radius ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        radius (commonPartitionCellLeftKnotIndex upper lower i) <
          radius (commonPartitionCellRightKnotIndex upper lower i)) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card,
        center j - radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val) ∧
        center j + radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val)) ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
            innerLower i ∧
          innerLower i <
            center (commonPartitionCellLeftKnotIndex upper lower i) -
              radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
          innerLower i <
            center (commonPartitionCellRightKnotIndex upper lower i) -
              radius (commonPartitionCellRightKnotIndex upper lower i) ∧
          center (commonPartitionCellLeftKnotIndex upper lower i) +
              radius (commonPartitionCellLeftKnotIndex upper lower i) <
            innerUpper i ∧
          center (commonPartitionCellRightKnotIndex upper lower i) +
              radius (commonPartitionCellRightKnotIndex upper lower i) <
            innerUpper i ∧
          innerUpper i <
            upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)) := by
  obtain ⟨center, radius, hcenter0, hradius0, hstep, hcores⟩ :=
    exists_commonPartitionEndpointCores upper lower hstart hsep
  have hstep' : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i) := by
    intro i
    have h := hstep i
    have hleft : commonPartitionCellLeftKnotIndex upper lower i =
        ⟨i.val, by omega⟩ := Fin.ext rfl
    have hright : commonPartitionCellRightKnotIndex upper lower i =
        ⟨i.val + 1, by
          have hcard := Nat.sub_add_cancel
            (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
          omega⟩ := Fin.ext rfl
    simpa [hleft, hright] using h
  have hbounds : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      ∃ lo hi : ℝ,
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) < lo ∧
        lo < center (commonPartitionCellLeftKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        lo < center (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
          radius (commonPartitionCellLeftKnotIndex upper lower i) < hi ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
          radius (commonPartitionCellRightKnotIndex upper lower i) < hi ∧
        hi < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
    intro i
    exact exists_commonPartitionCellInnerBounds upper lower center radius hcores i
  choose innerLower innerUpper hgeometry using hbounds
  refine ⟨center, radius, innerLower, innerUpper, ?_, ?_, hstep', hcores,
    hgeometry⟩
  · exact hcenter0
  · exact hradius0

/-- The same finite corridor geometry can be arranged with all endpoint
core radii below any prescribed positive tolerance. This is the parameter
that must tend to zero after the fixed-core logarithmic estimate. -/
theorem exists_commonPartitionLowerGeometry_small
    (upper lower : StepBoundary)
    (hstart : StartAdmissible upper lower)
    (hsep : TraceSeparated upper lower) {η : ℝ} (hη : 0 < η) :
    ∃ center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ,
      ∃ innerLower innerUpper :
        Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ,
      center ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      radius ⟨0, by
        have hcard := Finset.card_pos.mpr
          (StepBoundary.commonKnots_nonempty upper lower)
        omega⟩ = 0 ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        radius (commonPartitionCellLeftKnotIndex upper lower i) <
          radius (commonPartitionCellRightKnotIndex upper lower i)) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card, radius j < η) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card, 0 ≤ radius j) ∧
      (∀ j : Fin (StepBoundary.commonKnots upper lower).card,
        center j - radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val) ∧
        center j + radius j ∈ selValues upper lower
          (StepBoundary.commonPartitionGrid upper lower j.val)) ∧
      (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
            innerLower i ∧
          innerLower i <
            center (commonPartitionCellLeftKnotIndex upper lower i) -
              radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
          innerLower i <
            center (commonPartitionCellRightKnotIndex upper lower i) -
              radius (commonPartitionCellRightKnotIndex upper lower i) ∧
          center (commonPartitionCellLeftKnotIndex upper lower i) +
              radius (commonPartitionCellLeftKnotIndex upper lower i) <
            innerUpper i ∧
          center (commonPartitionCellRightKnotIndex upper lower i) +
              radius (commonPartitionCellRightKnotIndex upper lower i) <
            innerUpper i ∧
          innerUpper i <
            upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)) := by
  obtain ⟨center, radius, hcenter0, hradius0, hstep, hsmall,
      hradiusNonneg, hcores⟩ :=
    exists_commonPartitionEndpointCores_small upper lower hstart hsep hη
  have hstep' : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i) := by
    intro i
    have h := hstep i
    have hleft : commonPartitionCellLeftKnotIndex upper lower i =
        ⟨i.val, by omega⟩ := Fin.ext rfl
    have hright : commonPartitionCellRightKnotIndex upper lower i =
        ⟨i.val + 1, by
          have hcard := Nat.sub_add_cancel
            (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
          omega⟩ := Fin.ext rfl
    simpa [hleft, hright] using h
  have hbounds : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      ∃ lo hi : ℝ,
        lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) < lo ∧
        lo < center (commonPartitionCellLeftKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        lo < center (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
          radius (commonPartitionCellLeftKnotIndex upper lower i) < hi ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
          radius (commonPartitionCellRightKnotIndex upper lower i) < hi ∧
        hi < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
    intro i
    exact exists_commonPartitionCellInnerBounds upper lower center radius hcores i
  choose innerLower innerUpper hgeometry using hbounds
  exact ⟨center, radius, innerLower, innerUpper, hcenter0, hradius0, hstep',
    hsmall, hradiusNonneg, hcores, hgeometry⟩


end Skorokhod.PathClass.StepCorridor

end
