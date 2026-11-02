/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.Lower.Geometry
import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Partition.Lower.Kernel
import Topology.Cadlag.Skorokhod.Path.Scaling

/-!
# Internal geometry for the partition lower bound

These deterministic results support the finite-partition lower-bound proof.
They establish the return-window margins, construct the translated path on a
cell, transfer rational-coordinate bounds to the whole cell, and concatenate
cell events into the global corridor event.

## Internal proof declarations

* `commonPartitionCellCoreReturnBounds` places the translated return window
  strictly inside the cell corridor from the neighboring-core hypotheses.
* `commonPartitionCellIncrementPath` and
  `commonPartitionCellIncrementPath_apply` define the path translated and
  rescaled to one partition cell.
* `scaledNormalizedCellIocReturnEvent_implies_cellBounds` turns the
  rational-coordinate event into corridor bounds and an endpoint return bound
  on the full cell.
* `inter_commonPartitionCellCoreReturnEvent_subset_corridorSet` combines all
  cell events, together with the pinned-zero start, into the global scaled
  corridor event.

The cell constructions give the local-to-global event inclusion
\[
 \bigcap_{j<m} E_j\cap\{X(0)=0\}
   \subseteq \{X\text{ lies in the scaled global corridor}},
\]
with each $E_j$ supplying the full-cell corridor bounds and the endpoint
return on cell $j$.

-/

open MeasureTheory
open scoped Topology

section

namespace ProbabilityTheory

open Skorokhod.PathClass.StepCorridor

/-- The strict trace separation between neighboring cores makes the local
return interval a nonempty subinterval of the contracted cell corridor. -/
lemma commonPartitionCellCoreReturnBounds
    (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hgeometry :
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
    (hradius : radius (commonPartitionCellLeftKnotIndex upper lower i) <
      radius (commonPartitionCellRightKnotIndex upper lower i)) :
    let i₀ := commonPartitionCellLeftKnotIndex upper lower i
    let i₁ := commonPartitionCellRightKnotIndex upper lower i
    let lo := innerLower i + radius i₀ - center i₀
    let hi := innerUpper i - radius i₀ - center i₀
    let band := (radius i₁ - radius i₀) / 2
    lo < 0 ∧ 0 < hi ∧ lo < center i₁ - center i₀ - band ∧
      center i₁ - center i₀ - band < center i₁ - center i₀ + band ∧
      center i₁ - center i₀ + band < hi := by
  dsimp
  constructor
  · linarith [hgeometry.2.1]
  constructor
  · linarith [hgeometry.2.2.2.1]
  constructor
  · linarith [hgeometry.2.2.1, hradius]
  constructor
  · have hband : 0 <
        (radius (commonPartitionCellRightKnotIndex upper lower i) -
          radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2 :=
      half_pos (sub_pos.mpr hradius)
    linarith
  · linarith [hgeometry.2.2.2.2.1, hradius]

/-- The translated path restricted to one closed common-partition cell. -/
private noncomputable def commonPartitionCellIncrementPath
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (f : CadlagPath unitInterval ℝ) : CadlagPath unitInterval ℝ := by
  let φ : unitInterval → unitInterval := fun q =>
    StepBoundary.commonPartitionCellTime upper lower i.val q
  have hφmono : Monotone φ :=
    StepBoundary.monotone_commonPartitionCellTime upper lower i.val
  have hφc : Continuous φ := by
    apply Continuous.subtype_mk
    · change Continuous (fun q : unitInterval =>
        (StepBoundary.commonPartitionGrid upper lower i.val : ℝ) +
          (q : ℝ) * ((StepBoundary.commonPartitionGrid upper lower (i.val + 1) : ℝ) -
            (StepBoundary.commonPartitionGrid upper lower i.val : ℝ)))
      fun_prop
  refine ⟨fun q => f (φ q) - f (StepBoundary.commonPartitionGrid upper lower i.val), ?_⟩
  exact (f.compMonotoneContinuous φ hφmono hφc).isCadlag_toFun.continuous_comp
    (continuous_id.sub continuous_const)

@[simp]
private lemma commonPartitionCellIncrementPath_apply
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (f : CadlagPath unitInterval ℝ) (q : unitInterval) :
    commonPartitionCellIncrementPath upper lower i f q =
      f (StepBoundary.commonPartitionCellTime upper lower i.val q) -
        f (StepBoundary.commonPartitionGrid upper lower i.val) := rfl

/-- A local endpoint-return event gives the entire cell corridor and its
terminal return window. The rational uniform margin extends to all times by
the càdlàg dense-coordinate criterion. -/
private lemma scaledNormalizedCellIocReturnEvent_implies_cellBounds
    {α : ℝ} (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (f : CadlagPath unitInterval ℝ)
    {lo hi coreLo coreHi : ℝ}
    (hscale : 0 < commonPartitionCellSpatialScale α upper lower i)
    (hevent : f ∈ scaledNormalizedCellIocReturnEvent (α := α)
      upper lower i (commonPartitionCellSpatialScale α upper lower i)⁻¹
      lo hi coreLo coreHi) :
    (∀ q : unitInterval,
      lo < commonPartitionCellIncrementPath upper lower i f q ∧
      commonPartitionCellIncrementPath upper lower i f q < hi) ∧
      coreLo < commonPartitionCellIncrementPath upper lower i f ⊤ ∧
      commonPartitionCellIncrementPath upper lower i f ⊤ ≤ coreHi := by
  let spatial := commonPartitionCellSpatialScale α upper lower i
  let cell := commonPartitionCellIncrementPath upper lower i f
  have hcoord : (fun q : RationalCoordinate.UnitInterval =>
      spatial⁻¹ * normalizedCommonPartitionCellPath (α := α)
        upper lower i q f) ∈
      Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
        lo hi coreLo coreHi := by
    change f ∈ scaledNormalizedCellIocReturnEvent (α := α)
      upper lower i spatial⁻¹ lo hi coreLo coreHi at hevent
    exact hevent
  have hcoord' : (fun q : RationalCoordinate.UnitInterval =>
      cell (RationalCoordinate.toUnitInterval q)) ∈
      Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
        lo hi coreLo coreHi := by
    have hfun : (fun q : RationalCoordinate.UnitInterval =>
        spatial⁻¹ * normalizedCommonPartitionCellPath (α := α)
          upper lower i q f) =
        fun q => cell (RationalCoordinate.toUnitInterval q) := by
      funext q
      dsimp [cell, commonPartitionCellIncrementPath, spatial,
        normalizedCommonPartitionCellPath]
      rw [← mul_assoc, inv_mul_cancel₀ hscale.ne', one_mul]
    rw [hfun] at hcoord
    exact hcoord
  have hcorridor := (Skorokhod.mem_rationalCoordinateCorridorWithMargin_iff
    cell lo hi).mp hcoord'.1
  obtain ⟨margin, hmargin, hbound⟩ := hcorridor
  have htop : RationalCoordinate.toUnitInterval ⊤ = (⊤ : unitInterval) := by
    apply Subtype.ext
    norm_num [RationalCoordinate.toUnitInterval]
  have hreturn : cell ⊤ ∈ Set.Ioc coreLo coreHi := by
    simpa [htop] using hcoord'.2
  refine ⟨?_, ?_, ?_⟩
  · intro q
    have hq := hbound q
    constructor <;> linarith
  · exact hreturn.1
  · exact hreturn.2

/-- If every cell stays in its contracted inner strip and returns from the
incoming core to the next core, the whole path lies in the original strict
step corridor. The endpoint cores handle boundary jumps; cell interiors use
the right-continuous boundary value at the left knot. -/
lemma inter_commonPartitionCellCoreReturnEvent_subset_corridorSet
    {α : ℝ} {scale : ℝ} (upper lower : StepBoundary)
    (center radius : Fin (StepBoundary.commonKnots upper lower).card → ℝ)
    (innerLower innerUpper :
      Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hcenter0 : center ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hradius0 : radius ⟨0, by
      have hcard := Finset.card_pos.mpr
        (StepBoundary.commonKnots_nonempty upper lower)
      omega⟩ = 0)
    (hscale : 0 < scale)
    (hcores : ∀ j : Fin (StepBoundary.commonKnots upper lower).card,
      center j - radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val) ∧
      center j + radius j ∈ selValues upper lower
        (StepBoundary.commonPartitionGrid upper lower j.val))
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
    (f : CadlagPath unitInterval ℝ)
    (hstart : f ⊥ = 0)
    (hevents : f ∈ ⋂ i, commonPartitionCellCoreReturnEvent
      (α := α) scale upper lower center radius innerLower innerUpper i) :
    Skorokhod.scalePath scale f ∈ corridorSet upper lower := by
  let scaled := Skorokhod.scalePath scale f
  let knotCount := (StepBoundary.commonKnots upper lower).card
  have cellEventScaled (i : Fin (knotCount - 1)) :
      scaled ∈ scaledNormalizedCellIocReturnEvent (α := α) upper lower i
        (commonPartitionCellSpatialScale α upper lower i)⁻¹
        (innerLower i +
          radius (commonPartitionCellLeftKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i))
        (innerUpper i -
          radius (commonPartitionCellLeftKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i))
        (center (commonPartitionCellRightKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i) -
          (radius (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2)
        (center (commonPartitionCellRightKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i) +
          (radius (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) := by
    let i₀ := commonPartitionCellLeftKnotIndex upper lower i
    let i₁ := commonPartitionCellRightKnotIndex upper lower i
    let lo := innerLower i + radius i₀ - center i₀
    let hi := innerUpper i - radius i₀ - center i₀
    let band := (radius i₁ - radius i₀) / 2
    let coreLo := center i₁ - center i₀ - band
    let coreHi := center i₁ - center i₀ + band
    have hsource := Set.mem_iInter.mp hevents i
    have hsourceEvent : f ∈ scaledNormalizedCellIocReturnEvent (α := α)
        upper lower i (scale / commonPartitionCellSpatialScale α upper lower i)
        (innerLower i +
          radius (commonPartitionCellLeftKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i))
        (innerUpper i -
          radius (commonPartitionCellLeftKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i))
        (center (commonPartitionCellRightKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i) -
          (radius (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2)
        (center (commonPartitionCellRightKnotIndex upper lower i) -
          center (commonPartitionCellLeftKnotIndex upper lower i) +
          (radius (commonPartitionCellRightKnotIndex upper lower i) -
            radius (commonPartitionCellLeftKnotIndex upper lower i)) / 2) := by
      simpa [commonPartitionCellCoreReturnEvent,
        lo, hi, band, coreLo, coreHi] using hsource
    have hcoord : (fun q : RationalCoordinate.UnitInterval =>
        (scale / commonPartitionCellSpatialScale α upper lower i) *
          normalizedCommonPartitionCellPath (α := α) upper lower i q f) ∈
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin lo hi coreLo coreHi := by
      change (fun q : RationalCoordinate.UnitInterval =>
        (scale / commonPartitionCellSpatialScale α upper lower i) *
          normalizedCommonPartitionCellPath (α := α) upper lower i q f) ∈
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin lo hi coreLo coreHi
          at hsourceEvent
      exact hsourceEvent
    change (fun q : RationalCoordinate.UnitInterval =>
        (commonPartitionCellSpatialScale α upper lower i)⁻¹ *
          normalizedCommonPartitionCellPath (α := α) upper lower i q scaled) ∈
        Skorokhod.rationalCoordinateCorridorIocReturnWithMargin lo hi coreLo coreHi
    have hfun : (fun q : RationalCoordinate.UnitInterval =>
        (commonPartitionCellSpatialScale α upper lower i)⁻¹ *
          normalizedCommonPartitionCellPath (α := α) upper lower i q scaled) =
        fun q => (scale / commonPartitionCellSpatialScale α upper lower i) *
          normalizedCommonPartitionCellPath (α := α) upper lower i q f := by
      funext q
      dsimp [normalizedCommonPartitionCellPath, scaled, Skorokhod.scalePath]
      field_simp [ne_of_gt (commonPartitionCellSpatialScale_pos α upper lower i)]
    rw [hfun]
    exact hcoord
  have endpointCore : ∀ k : ℕ, (hk : k < knotCount) →
      center ⟨k, by simpa [knotCount] using hk⟩ -
          radius ⟨k, by simpa [knotCount] using hk⟩ ≤
          scaled (StepBoundary.commonPartitionGrid upper lower k) ∧
          scaled (StepBoundary.commonPartitionGrid upper lower k) ≤
          center ⟨k, by simpa [knotCount] using hk⟩ +
            radius ⟨k, by simpa [knotCount] using hk⟩ := by
    intro k
    induction k with
    | zero =>
        intro hk
        have hgrid := StepBoundary.commonPartitionGrid_zero upper lower
        rw [hgrid]
        change center ⟨0, by simpa [knotCount] using hk⟩ -
            radius ⟨0, by simpa [knotCount] using hk⟩ ≤
              scale * f ⊥ ∧
          scale * f ⊥ ≤ center ⟨0, by simpa [knotCount] using hk⟩ +
            radius ⟨0, by simpa [knotCount] using hk⟩
        rw [hcenter0, hradius0, hstart]
        simp
    | succ k ih =>
        intro hk
        have hkCard : k + 1 < (StepBoundary.commonKnots upper lower).card := by
          simpa [knotCount] using hk
        have hkCell' : k < (StepBoundary.commonKnots upper lower).card - 1 := by omega
        have hkCell : k < knotCount - 1 := by simpa [knotCount] using hkCell'
        let i : Fin (knotCount - 1) := ⟨k, hkCell⟩
        let i₀ := commonPartitionCellLeftKnotIndex upper lower i
        let i₁ := commonPartitionCellRightKnotIndex upper lower i
        have hprevBound : k < knotCount := by
          simpa [knotCount] using (Nat.lt_of_succ_lt hkCard)
        have hprev := ih hprevBound
        have hreturn := (scaledNormalizedCellIocReturnEvent_implies_cellBounds
          (α := α) upper lower i scaled
          (commonPartitionCellSpatialScale_pos α upper lower i)
          (cellEventScaled i)).2
        have hradius : radius i₀ < radius i₁ := by
          exact hradiusStep i
        have hstep : 0 < radius i₁ - radius i₀ := sub_pos.mpr hradius
        have hreturn' :
          center i₁ - center i₀ - (radius i₁ - radius i₀) / 2 <
              scaled (StepBoundary.commonPartitionGrid upper lower (k + 1)) -
                scaled (StepBoundary.commonPartitionGrid upper lower k) ∧
            scaled (StepBoundary.commonPartitionGrid upper lower (k + 1)) -
                scaled (StepBoundary.commonPartitionGrid upper lower k) ≤
              center i₁ - center i₀ + (radius i₁ - radius i₀) / 2 := by
          simpa [commonPartitionCellIncrementPath_apply,
            StepBoundary.commonPartitionCellTime_top, i, i₀, i₁] using hreturn
        have hnext := add_mem_nextCore_of_endpointBand
          (by
            have hi₀ : i₀ = ⟨k, by simpa [knotCount] using hprevBound⟩ := Fin.ext rfl
            simpa [hi₀] using hprev.1)
          (by
            have hi₀ : i₀ = ⟨k, by simpa [knotCount] using hprevBound⟩ := Fin.ext rfl
            simpa [hi₀] using hprev.2)
          (half_pos hstep)
          ((half_lt_self_iff).2 hstep)
          hreturn'.1 hreturn'.2
        constructor
        · have hi₁ : i₁ = ⟨k + 1, by simpa [knotCount] using hk⟩ := Fin.ext rfl
          exact le_of_lt (by simpa [hi₁] using hnext.1)
        · have hi₁ : i₁ = ⟨k + 1, by simpa [knotCount] using hk⟩ := Fin.ext rfl
          exact (by simpa [hi₁] using hnext.2.le)
  have knotCorridor (t : unitInterval) (ht : t ∈ StepBoundary.commonKnots upper lower) :
      lower.eval t < (scaled t : EReal) ∧ (scaled t : EReal) < upper.eval t := by
    obtain ⟨j, hj⟩ := StepBoundary.exists_fin_commonPartitionGrid_eq upper lower ht
    have hend := endpointCore j.val j.isLt
    have hlowTrace : lower.rightTrace
        (StepBoundary.commonPartitionGrid upper lower j.val) <
          (center j - radius j : EReal) := by
      exact (le_max_right _ _).trans_lt ((hcores j).1.1)
    have hupperTrace : (center j + radius j : EReal) <
        upper.rightTrace (StepBoundary.commonPartitionGrid upper lower j.val) := by
      exact (lt_of_lt_of_le ((hcores j).2.2) (min_le_right _ _))
    have hendLower : (center j - radius j : EReal) ≤
        (scaled (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) :=
      EReal.coe_le_coe_iff.mpr hend.1
    have hendUpper : (scaled (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) ≤
        (center j + radius j : EReal) :=
      EReal.coe_le_coe_iff.mpr hend.2
    constructor
    · calc
        lower.eval t = lower.rightTrace
            (StepBoundary.commonPartitionGrid upper lower j.val) := by
              rw [← hj, StepBoundary.rightTrace_eq_eval]
        _ < (center j - radius j : EReal) := hlowTrace
        _ ≤ (scaled (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) := hendLower
        _ = (scaled t : EReal) := by rw [hj]
    · calc
        (scaled t : EReal) =
            (scaled (StepBoundary.commonPartitionGrid upper lower j.val) : EReal) := by
          rw [hj]
        _ ≤ (center j + radius j : EReal) := hendUpper
        _ < upper.rightTrace (StepBoundary.commonPartitionGrid upper lower j.val) := hupperTrace
        _ = upper.eval t := by rw [← hj, StepBoundary.rightTrace_eq_eval]
  have hcorridor (t : unitInterval) :
      lower.eval t < (scaled t : EReal) ∧ (scaled t : EReal) < upper.eval t := by
    by_cases ht : t ∈ StepBoundary.commonKnots upper lower
    · exact knotCorridor t ht
    · have htbot : t ≠ ⊥ := by
        intro h
        apply ht
        simp [h]
      have httop : t ≠ ⊤ := by
        intro h
        apply ht
        simp [h]
      have hinterior : t ∈ Set.Ioo (⊥ : unitInterval) ⊤ :=
        ⟨bot_lt_iff_ne_bot.mpr htbot, lt_top_iff_ne_top.mpr httop⟩
      have hnotSet : t ∉ (StepBoundary.commonKnots upper lower : Set unitInterval) := by
        simpa using ht
      have hcellUnion : t ∈ StepBoundary.commonCellUnion upper lower :=
        (StepBoundary.iUnion_commonCells_eq upper lower).symm ▸
          ⟨hinterior, hnotSet⟩
      change t ∈ ⋃ (p : unitInterval)
        (_ : p ∈ ((StepBoundary.commonKnots upper lower).erase ⊤ : Set unitInterval)),
          StepBoundary.commonCell upper lower p at hcellUnion
      obtain ⟨p, hp, hpt⟩ := Set.mem_iUnion₂.mp hcellUnion
      rcases Finset.mem_erase.mp hp with ⟨hpTop, hpMem⟩
      have hcell : p < t ∧ t < StepBoundary.nextCommonKnot upper lower p hpTop := by
        simpa [StepBoundary.commonCell, hpTop] using hpt
      obtain ⟨j, hj⟩ := StepBoundary.exists_fin_commonPartitionGrid_eq
        upper lower hpMem
      have hjlt : j.val < knotCount - 1 := by
        by_contra hnotlt
        have hjlast : j.val = knotCount - 1 := by omega
        have hgridTop : StepBoundary.commonPartitionGrid upper lower j.val = ⊤ := by
          calc
            _ = StepBoundary.commonPartitionGrid upper lower (knotCount - 1) := by rw [hjlast]
            _ = ⊤ := StepBoundary.commonPartitionGrid_last upper lower
        have hpeq : p = ⊤ := hj.symm.trans hgridTop
        exact hpTop hpeq
      let i : Fin (knotCount - 1) := ⟨j.val, hjlt⟩
      have hleftStrict : StepBoundary.commonPartitionGrid upper lower i.val < t := by
        simpa [i, hj] using hcell.1
      have hnotTop : StepBoundary.commonPartitionGrid upper lower i.val ≠ ⊤ :=
        ne_of_lt (lt_of_lt_of_le
          (StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt) le_top)
      have hcellNext : t < StepBoundary.nextCommonKnot upper lower
          (StepBoundary.commonPartitionGrid upper lower i.val) hnotTop := by
        subst p
        simpa [i] using hcell.2
      have hnextEq := StepBoundary.nextCommonKnot_eq_commonPartitionGrid_succ
        upper lower i
      have hrightStrict : t <
          StepBoundary.commonPartitionGrid upper lower (i.val + 1) := by
        simpa [hnextEq] using hcellNext
      have hleft : StepBoundary.commonPartitionGrid upper lower i.val ≤ t := hleftStrict.le
      obtain ⟨q, hq⟩ := StepBoundary.exists_commonPartitionCellTime_eq
        upper lower i hleft hrightStrict.le
      let i₀ := commonPartitionCellLeftKnotIndex upper lower i
      let i₁ := commonPartitionCellRightKnotIndex upper lower i
      have hstartCore := endpointCore i₀.val i₀.isLt
      have hlocal := (scaledNormalizedCellIocReturnEvent_implies_cellBounds
        (α := α) upper lower i scaled
        (commonPartitionCellSpatialScale_pos α upper lower i)
        (cellEventScaled i)).1 q
      have hlocal' :
          innerLower i + radius i₀ - center i₀ < scaled t -
            scaled (StepBoundary.commonPartitionGrid upper lower i.val) ∧
          scaled t - scaled (StepBoundary.commonPartitionGrid upper lower i.val) <
            innerUpper i - radius i₀ - center i₀ := by
          simpa [commonPartitionCellIncrementPath_apply, hq, i₀, i] using hlocal
      have hrealLower : innerLower i < scaled t := by
        have hstartCore' : center i₀ - radius i₀ ≤
            scaled (StepBoundary.commonPartitionGrid upper lower i.val) := by
          have hindex : i₀ = ⟨j.val, by omega⟩ := Fin.ext rfl
          simpa [hindex, i] using hstartCore.1
        linarith [hlocal'.1]
      have hrealUpper : scaled t < innerUpper i := by
        have hstartCore' : scaled (StepBoundary.commonPartitionGrid upper lower i.val) ≤
            center i₀ + radius i₀ := by
          have hindex : i₀ = ⟨j.val, by omega⟩ := Fin.ext rfl
          simpa [hindex, i] using hstartCore.2
        linarith [hlocal'.2]
      have hlowEval := StepBoundary.lower_eval_eq_rightTrace_on_nextCell
        upper lower (StepBoundary.commonPartitionGrid upper lower i.val) t
        hnotTop hleftStrict hcellNext
      have hupperEval := StepBoundary.upper_eval_eq_rightTrace_on_nextCell
        upper lower (StepBoundary.commonPartitionGrid upper lower i.val) t
        hnotTop hleftStrict hcellNext
      constructor
      · rw [hlowEval]
        exact (hgeometry i).1.trans (EReal.coe_lt_coe_iff.mpr hrealLower)
      · rw [hupperEval]
        exact (EReal.coe_lt_coe_iff.mpr hrealUpper).trans (hgeometry i).2.2.2.2.2
  change scaled ⊥ = 0 ∧ ∀ t, lower.eval t < (scaled t : EReal) ∧
    (scaled t : EReal) < upper.eval t
  exact ⟨by simp [scaled, Skorokhod.scalePath, hstart], hcorridor⟩

end ProbabilityTheory

end
