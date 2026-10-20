/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Boundary.Partition
import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Partition.LowerGeometry

/-!
# Core contraction step for the stable partition-rate proof

Given $0<\theta\leq1$, replacing every endpoint radius $r_j$ by
$\theta r_j$ preserves trace containment, strict increase between adjacent
knots, and the finite inner-cell inequalities. This supports the limiting
argument in the stable partition lower-rate assembly.

- `ProbabilityTheory.commonPartitionLowerGeometry_shrinkCore` proves these
  three preservation conclusions for a fixed step corridor.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

open Skorokhod.PathClass.StepCorridor

/-- Shrinking every endpoint core by the same factor in `(0,1]` preserves
the fixed finite inner corridors and all trace containments. The strict radius
growth is also preserved. This is the quantitative order needed to remove
the incoming-core loss from the cell rates. -/
lemma commonPartitionLowerGeometry_shrinkCore
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
    (hradiusNonneg : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      0 ≤ radius j)
    (hradiusStep : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      radius (commonPartitionCellLeftKnotIndex upper lower i) <
        radius (commonPartitionCellRightKnotIndex upper lower i))
    (hgeometry : ∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
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
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val))
    {θ : ℝ} (hθ : 0 < θ) (hθle : θ ≤ 1) :
    (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      θ * radius (commonPartitionCellLeftKnotIndex upper lower i) <
        θ * radius (commonPartitionCellRightKnotIndex upper lower i)) ∧
    (∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - θ * radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + θ * radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val)) ∧
    (∀ i : Fin ((StepBoundary.commonKnots upper lower).card - 1),
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) <
          innerLower i ∧
        innerLower i <
          center (commonPartitionCellLeftKnotIndex upper lower i) -
            θ * radius (commonPartitionCellLeftKnotIndex upper lower i) ∧
        innerLower i <
          center (commonPartitionCellRightKnotIndex upper lower i) -
            θ * radius (commonPartitionCellRightKnotIndex upper lower i) ∧
        center (commonPartitionCellLeftKnotIndex upper lower i) +
            θ * radius (commonPartitionCellLeftKnotIndex upper lower i) <
          innerUpper i ∧
        center (commonPartitionCellRightKnotIndex upper lower i) +
            θ * radius (commonPartitionCellRightKnotIndex upper lower i) <
          innerUpper i ∧
        innerUpper i <
          upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact mul_lt_mul_of_pos_left (hradiusStep i) hθ
  · intro j
    have hshrink : θ * radius j ≤ radius j := by
      calc
        θ * radius j ≤ 1 * radius j :=
          mul_le_mul_of_nonneg_right hθle (hradiusNonneg j)
        _ = radius j := one_mul _
    have hlow : (center j - radius j : EReal) ≤
        (center j - θ * radius j : EReal) :=
      EReal.coe_le_coe_iff.mpr (by linarith)
    have hhigh : (center j + θ * radius j : EReal) ≤
        (center j + radius j : EReal) :=
      EReal.coe_le_coe_iff.mpr (by linarith)
    have hlowOther : (center j - θ * radius j : EReal) <
        min (upper.leftTrace (StepBoundary.commonPartitionGrid upper lower j.val))
          (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower j.val)) := by
      have hcenterLe : (center j - θ * radius j : EReal) ≤
          (center j + radius j : EReal) :=
        EReal.coe_le_coe_iff.mpr (by nlinarith [hθ, hradiusNonneg j])
      exact hcenterLe.trans_lt (hcores j).2.2
    have hhighOther : max
        (lower.leftTrace (StepBoundary.commonPartitionGrid upper lower j.val))
        (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower j.val)) <
          (center j + θ * radius j : EReal) := by
      have hcenterLe : (center j - radius j : EReal) ≤
          (center j + θ * radius j : EReal) :=
        EReal.coe_le_coe_iff.mpr (by nlinarith [hθ, hradiusNonneg j])
      exact (hcores j).1.1.trans_le hcenterLe
    exact ⟨⟨(hcores j).1.1.trans_le hlow, hlowOther⟩,
      ⟨hhighOther, hhigh.trans_lt (hcores j).2.2⟩⟩
  · intro i
    let i₀ := commonPartitionCellLeftKnotIndex upper lower i
    let i₁ := commonPartitionCellRightKnotIndex upper lower i
    have hshrink₀ : θ * radius i₀ ≤ radius i₀ := by
      calc
        θ * radius i₀ ≤ 1 * radius i₀ :=
          mul_le_mul_of_nonneg_right hθle (hradiusNonneg i₀)
        _ = radius i₀ := one_mul _
    have hshrink₁ : θ * radius i₁ ≤ radius i₁ := by
      calc
        θ * radius i₁ ≤ 1 * radius i₁ :=
          mul_le_mul_of_nonneg_right hθle (hradiusNonneg i₁)
        _ = radius i₁ := one_mul _
    refine ⟨(hgeometry i).1, ?_, ?_, ?_, ?_, (hgeometry i).2.2.2.2.2⟩
    · exact (hgeometry i).2.1.trans_le (by linarith)
    · exact (hgeometry i).2.2.1.trans_le (by linarith)
    · exact (by linarith [(hgeometry i).2.2.2.1] :
        center i₀ + θ * radius i₀ < innerUpper i)
    · exact (by linarith [(hgeometry i).2.2.2.2.1] :
        center i₁ + θ * radius i₁ < innerUpper i)


end ProbabilityTheory

end
