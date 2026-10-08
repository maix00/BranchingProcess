/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.Independence
public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Basic
public import Topology.Cadlag.Skorokhod.Oscillation.Dense

/-!
# Closed range bounds on common partition cells

Each open cell uses rational times strictly before its right knot. A closed
oscillation bound on those coordinates handles left limits at a boundary jump
without imposing the post-jump constraint on the preceding cell.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The translated path on a common boundary cell, observed at rational
coordinates strictly before its right endpoint. -/
noncomputable def commonPartitionCellPath
    {Ω : Type*} {X : unitInterval → Ω → ℝ}
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Ω → CellInteriorCoordinate → ℝ :=
  fun ω q =>
    X (StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval q.val)) ω -
      X (StepBoundary.commonPartitionGrid upper lower i.val) ω

/-- The local range event imposes only a closed pairwise oscillation bound on
the half-open cell. -/
def commonPartitionCellRangeBound (width : ℝ) :
    Set (CellInteriorCoordinate → ℝ) :=
  {f | ∀ s t : CellInteriorCoordinate, |f s - f t| ≤ width}

theorem measurableSet_commonPartitionCellRangeBound (width : ℝ) :
    MeasurableSet (commonPartitionCellRangeBound width) := by
  classical
  change MeasurableSet
    {f : CellInteriorCoordinate → ℝ | ∀ s t, |f s - f t| ≤ width}
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun s => by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun t => by
      have h : Measurable
          (fun f : CellInteriorCoordinate → ℝ => |f s - f t|) := by
        fun_prop
      exact measurableSet_le h measurable_const

/-- A sample-space event that the translated path stays within a closed
range-diameter bound on one half-open common cell. -/
def commonPartitionCellRangeEvent
    {Ω : Type*} {X : unitInterval → Ω → ℝ}
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (width : ℝ) : Set Ω :=
  (commonPartitionCellPath (X := X) upper lower i) ⁻¹'
    commonPartitionCellRangeBound width

/-- Mutual independence of the translated cell paths factors intersections
of cell range events, even when each cell has a different width. -/
theorem measure_iInter_commonPartitionCellRangeEvent_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] {X : unitInterval → Ω → ℝ}
    {P : Measure Ω} {upper lower : StepBoundary}
    (hindep : iIndepFun (commonPartitionCellPath (X := X) upper lower) P)
    (width : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ) :
    P (⋂ i, commonPartitionCellRangeEvent (X := X) upper lower i (width i)) =
      ∏ i, P (commonPartitionCellRangeEvent (X := X) upper lower i (width i)) := by
  have hfactor := hindep.measure_inter_preimage_eq_mul
    (Finset.univ : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (sets := fun i => commonPartitionCellRangeBound (width i))
    (by
      intro i hi
      exact measurableSet_commonPartitionCellRangeBound (width i))
  simpa [commonPartitionCellRangeEvent] using hfactor

/-- Factorization on any selected finite set of common cells. This lets the
upper estimate omit infinite-width cells, whose rate cost is zero. -/
theorem measure_biInter_commonPartitionCellRangeEvent_eq_prod
    {Ω : Type*} [MeasurableSpace Ω] {X : unitInterval → Ω → ℝ}
    {P : Measure Ω} {upper lower : StepBoundary}
    (hindep : iIndepFun (commonPartitionCellPath (X := X) upper lower) P)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (width : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ) :
    P (⋂ i ∈ s, commonPartitionCellRangeEvent (X := X)
        upper lower i (width i)) =
      ∏ i ∈ s, P (commonPartitionCellRangeEvent (X := X)
        upper lower i (width i)) := by
  have hfactor := hindep.measure_inter_preimage_eq_mul s
    (sets := fun i => commonPartitionCellRangeBound (width i))
    (by
      intro i hi
      exact measurableSet_commonPartitionCellRangeBound (width i))
  simpa [commonPartitionCellRangeEvent] using hfactor

private theorem eval_eq_rightTrace_at_cellCoordinate
    (b upper lower : StepBoundary)
    (hknots : ∀ r ∈ b.knots, r ∈ StepBoundary.commonKnots upper lower)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (q : CellInteriorCoordinate) :
    b.eval (StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval q.val)) =
      b.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) := by
  let s := StepBoundary.commonPartitionCellTime upper lower i.val
    (RationalCoordinate.toUnitInterval q.val)
  by_cases hleftEq : s = StepBoundary.commonPartitionGrid upper lower i.val
  · simp [s, hleftEq, StepBoundary.rightTrace_eq_eval]
  · have hleftLe := StepBoundary.commonPartitionCellTime_left_le upper lower i.val
      (RationalCoordinate.toUnitInterval q.val)
    have hleft : StepBoundary.commonPartitionGrid upper lower i.val < s :=
      lt_of_le_of_ne hleftLe (Ne.symm hleftEq)
    have hqright : RationalCoordinate.toUnitInterval q.val < ⊤ := by
      change ((q.val : ℚ) : ℝ) < 1
      exact_mod_cast q.property
    have hright := StepBoundary.commonPartitionCellTime_lt_right upper lower
      i.val i.isLt (RationalCoordinate.toUnitInterval q.val) hqright
    exact StepBoundary.eval_eq_rightTrace_on_commonPartitionCell
      b upper lower hknots i.val i.isLt hleft hright

/-- A strict step corridor with finite bounds on one common cell forces the
closed range-diameter bound on that half-open cell. The terminal coordinate
is excluded, so a jump at the right knot uses the next cell's boundary. -/
theorem corridorSet_subset_commonPartitionCellRangeEvent_of_finiteBounds
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    {lo hi : ℝ}
    (hlower : lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo : EReal))
    (hupper : upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi : EReal))
    (_hwidth : lo < hi) :
    corridorSet upper lower ⊆
      commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (hi - lo) := by
  intro f hf
  change commonPartitionCellPath
      (X := fun t (f : CadlagPath unitInterval ℝ) => f t) upper lower i f ∈
    commonPartitionCellRangeBound (hi - lo)
  change f ⊥ = 0 ∧ ∀ t : unitInterval,
    lower.eval t < (f t : EReal) ∧ (f t : EReal) < upper.eval t at hf
  rcases hf with ⟨_, hcorridor⟩
  simp only [commonPartitionCellRangeBound]
  intro s t
  dsimp [commonPartitionCellPath]
  let τ (q : CellInteriorCoordinate) :=
    StepBoundary.commonPartitionCellTime upper lower i.val
      (RationalCoordinate.toUnitInterval q.val)
  have hslower := hcorridor (τ s)
  have htlower := hcorridor (τ t)
  rw [eval_eq_rightTrace_at_cellCoordinate lower upper lower
    (fun r hr => StepBoundary.mem_commonKnots_of_mem_lower upper lower hr)
    i s, hlower] at hslower
  rw [eval_eq_rightTrace_at_cellCoordinate upper upper lower
    (fun r hr => StepBoundary.mem_commonKnots_of_mem_upper upper lower hr)
    i s, hupper] at hslower
  rw [eval_eq_rightTrace_at_cellCoordinate lower upper lower
    (fun r hr => StepBoundary.mem_commonKnots_of_mem_lower upper lower hr)
    i t, hlower] at htlower
  rw [eval_eq_rightTrace_at_cellCoordinate upper upper lower
    (fun r hr => StepBoundary.mem_commonKnots_of_mem_upper upper lower hr)
    i t, hupper] at htlower
  have hlos : lo < f (τ s) := EReal.coe_lt_coe_iff.mp hslower.1
  have hhis : f (τ s) < hi := EReal.coe_lt_coe_iff.mp hslower.2
  have hlot : lo < f (τ t) := EReal.coe_lt_coe_iff.mp htlower.1
  have hhit : f (τ t) < hi := EReal.coe_lt_coe_iff.mp htlower.2
  have hosc : |f (τ s) - f (τ t)| ≤ hi - lo := by
    rw [abs_le]
    constructor <;> linarith
  simpa [τ] using hosc

/-- A corridor is contained in the intersection of its finite-width cell
range events. The selected finite set and its real bounds are supplied by the
caller; cells with an infinite side are omitted. -/
theorem corridorSet_subset_biInter_commonPartitionCellRangeEvents
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s, lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo i : EReal))
    (hupper : ∀ i ∈ s, upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi i : EReal))
    (hwidth : ∀ i ∈ s, lo i < hi i) :
    corridorSet upper lower ⊆
      ⋂ i ∈ s, commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (hi i - lo i) := by
  intro f hf
  simp only [Set.mem_iInter]
  intro i hiMem
  exact corridorSet_subset_commonPartitionCellRangeEvent_of_finiteBounds
    upper lower i (hlower i hiMem) (hupper i hiMem) (hwidth i hiMem) hf

/-- The probability of a corridor is bounded by the product of its local
closed range probabilities on any selected finite set of finite-width cells.
The product identity is supplied by independent translated cell paths. -/
theorem measure_corridorSet_le_commonPartitionCellRangeProduct
    {P : Measure (CadlagPath unitInterval ℝ)}
    (upper lower : StepBoundary)
    (s : Finset (Fin ((StepBoundary.commonKnots upper lower).card - 1)))
    (lo hi : Fin ((StepBoundary.commonKnots upper lower).card - 1) → ℝ)
    (hlower : ∀ i ∈ s, lower.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (lo i : EReal))
    (hupper : ∀ i ∈ s, upper.rightTrace
      (StepBoundary.commonPartitionGrid upper lower i.val) = (hi i : EReal))
    (hwidth : ∀ i ∈ s, lo i < hi i)
    (hindep : iIndepFun
      (commonPartitionCellPath
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t) upper lower) P) :
    P (corridorSet upper lower) ≤
      ∏ i ∈ s, P (commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (hi i - lo i)) := by
  calc
    P (corridorSet upper lower) ≤ P (⋂ i ∈ s,
        commonPartitionCellRangeEvent
          (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
          upper lower i (hi i - lo i)) :=
      measure_mono (corridorSet_subset_biInter_commonPartitionCellRangeEvents
        upper lower s lo hi hlower hupper hwidth)
    _ = ∏ i ∈ s, P (commonPartitionCellRangeEvent
        (X := fun t (f : CadlagPath unitInterval ℝ) => f t)
        upper lower i (hi i - lo i)) :=
      measure_biInter_commonPartitionCellRangeEvent_eq_prod
        hindep s (fun i => hi i - lo i)

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

end
