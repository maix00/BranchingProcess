/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Path.Skorokhod.RationalTime
import Topology.Order.UnitInterval.Rational

/-!
# Uniform rational block restrictions

This module contains the path-level part of a uniform corridor partition.
It is independent of stable laws and of any particular process: a path on
rational times is cut into translated block paths, and the resulting tube
events are measurable.  Generic measure bounds for independent block paths
live in `UniformBlocks.Probability`; stable Lévy processes supply the block
laws and independence in `Probability.Process.Stable.SmallDeviation.Blocks`.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- The `q` coordinate inside the `j`th block of a uniform partition of the
unit interval, represented as a rational point of the unit interval. -/
def rationalUniformBlockTime {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑RationalCoordinate.UnitInterval) :
    ↑RationalCoordinate.UnitInterval :=
  ⟨((j.val : ℚ) + (q : ℚ)) / (blocks : ℚ), by
    have hden : 0 < (blocks : ℚ) := by exact_mod_cast hblocks
    have hnum0 : 0 ≤ (j.val : ℚ) + (q : ℚ) :=
      add_nonneg (by positivity) q.property.1
    have hj : (j.val : ℚ) + 1 ≤ (blocks : ℚ) := by
      exact_mod_cast (Nat.succ_le_of_lt j.isLt)
    have hnum : (j.val : ℚ) + (q : ℚ) ≤ (blocks : ℚ) := by
      linarith [q.property.2]
    constructor
    · exact div_nonneg hnum0 hden.le
    · rw [div_le_iff₀ hden]
      simpa using hnum⟩

/-- The time embedding for one rational block is monotone. -/
theorem monotone_rationalUniformBlockTime {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) :
    Monotone (rationalUniformBlockTime hblocks j) := by
  intro s t hst
  apply Subtype.mk_le_mk.mpr
  have hden : 0 < (blocks : ℚ) := by exact_mod_cast hblocks
  change (s : ℚ) ≤ t at hst
  change ((j.val : ℚ) + (s : ℚ)) / (blocks : ℚ) ≤
    ((j.val : ℚ) + (t : ℚ)) / (blocks : ℚ)
  exact (div_le_div_iff_of_pos_right hden).2 (by linarith)

/-- The uniform block time map preserves the initial rational time. -/
@[simp]
theorem rationalUniformBlockTime_bot {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) :
    rationalUniformBlockTime hblocks j ⊥ = ⟨(j.val : ℚ) / (blocks : ℚ), by
      constructor
      · positivity
      · rw [div_le_iff₀ (by exact_mod_cast hblocks : 0 < (blocks : ℚ))]
        norm_num [one_mul]
      ⟩ := by
  apply Subtype.ext
  simp [rationalUniformBlockTime]

/-- The real-time endpoint of a rational point in a uniform block. -/
def rationalUniformBlockAbsoluteTime {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑RationalCoordinate.UnitInterval) : ℝ≥0 :=
  RationalCoordinate.toNNReal (rationalUniformBlockTime hblocks j q)

/-- The translated block path obtained by restricting a real-time process to
one uniform block and subtracting its value at the block's left endpoint.
This construction has no assumption on the law of the process. -/
def rationalUniformBlockProcessFromTime {Ω : Type*}
    (X : ℝ≥0 → Ω → ℝ) {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) : ↑RationalCoordinate.UnitInterval → Ω → ℝ :=
  fun q ω => X (rationalUniformBlockAbsoluteTime hblocks j q) ω -
    X (rationalUniformBlockAbsoluteTime hblocks j ⊥) ω

/-- The real-time boundary after `m` blocks of a uniform partition. -/
noncomputable def rationalUniformBlockBoundary (blocks m : ℕ)
    (hblocks : 0 < blocks) : ℝ≥0 :=
  ⟨(m : ℝ) / (blocks : ℝ), by positivity⟩

theorem rationalUniformBlockBoundary_eq_start {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    rationalUniformBlockBoundary blocks j.val hblocks =
      rationalUniformBlockAbsoluteTime hblocks j ⊥ := by
  apply NNReal.coe_injective
  simp only [rationalUniformBlockBoundary, rationalUniformBlockAbsoluteTime,
    RationalCoordinate.toNNReal_coe, rationalUniformBlockTime_bot]
  change (j.val : ℝ) / (blocks : ℝ) =
    (((j.val : ℚ) / (blocks : ℚ) : ℚ) : ℝ)
  push_cast
  rfl

/-- The boundary after block `j` is its right endpoint. -/
theorem rationalUniformBlockBoundary_succ_eq_end {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    rationalUniformBlockBoundary blocks (j.val + 1) hblocks =
      rationalUniformBlockAbsoluteTime hblocks j ⊤ := by
  apply NNReal.coe_injective
  change ((j.val + 1 : ℕ) : ℝ) / (blocks : ℝ) =
    (((((j.val : ℚ) + 1) / (blocks : ℚ)) : ℚ) : ℝ)
  push_cast
  rfl

theorem monotone_rationalUniformBlockAbsoluteTime {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    Monotone (rationalUniformBlockAbsoluteTime hblocks j) := by
  intro s t hst
  apply NNReal.coe_le_coe.mp
  change ((rationalUniformBlockTime hblocks j s : ℚ) : ℝ) ≤
    ((rationalUniformBlockTime hblocks j t : ℚ) : ℝ)
  exact_mod_cast monotone_rationalUniformBlockTime hblocks j hst

theorem rationalUniformBlockAbsoluteTime_le_boundary {blocks : ℕ}
    (hblocks : 0 < blocks) (k : Fin blocks) (m : ℕ)
    (hkm : k.val < m) (q : ↑RationalCoordinate.UnitInterval) :
    rationalUniformBlockAbsoluteTime hblocks k q ≤
      rationalUniformBlockBoundary blocks m hblocks := by
  apply NNReal.coe_le_coe.mp
  change ((((k.val : ℚ) + (q : ℚ)) / (blocks : ℚ) : ℚ) : ℝ) ≤
    (m : ℝ) / (blocks : ℝ)
  have hden : 0 < (blocks : ℚ) := by exact_mod_cast hblocks
  have hq : (q : ℚ) ≤ 1 := q.property.2
  have hkmQ : (k.val : ℚ) + 1 ≤ (m : ℚ) := by
    exact_mod_cast (Nat.succ_le_of_lt hkm)
  have hrat : ((k.val : ℚ) + (q : ℚ)) / (blocks : ℚ) ≤
      (m : ℚ) / (blocks : ℚ) :=
    (div_le_div_iff_of_pos_right hden).2 (by linarith)
  calc
    ((((k.val : ℚ) + (q : ℚ)) / (blocks : ℚ) : ℚ) : ℝ) ≤
        (((m : ℚ) / (blocks : ℚ) : ℚ) : ℝ) := by exact_mod_cast hrat
    _ = (m : ℝ) / (blocks : ℝ) := by push_cast; rfl

/-- The first uniform block has horizon `1 / blocks`. -/
theorem rationalUniformBlockAbsoluteTime_zero_eq_horizon
    {blocks : ℕ} (hblocks : 0 < blocks)
    (q : ↑RationalCoordinate.UnitInterval) :
    rationalUniformBlockAbsoluteTime hblocks ⟨0, hblocks⟩ q =
      rationalUniformBlockBoundary blocks 1 hblocks * RationalCoordinate.toNNReal q := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul]
  norm_num [rationalUniformBlockAbsoluteTime, rationalUniformBlockBoundary,
    RationalCoordinate.toNNReal, rationalUniformBlockTime, RationalCoordinate.toUnitInterval]
  change (((q : ℚ) : ℝ) / (blocks : ℝ)) =
    (blocks : ℝ)⁻¹ * ((q : ℚ) : ℝ)
  ring

theorem rationalUniformBlockProcess_zero_eq_initial
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    (fun ω q => rationalUniformBlockProcessFromTime X hblocks
      ⟨0, hblocks⟩ q ω) =
      (fun ω q => X (rationalUniformBlockBoundary blocks 1 hblocks *
        RationalCoordinate.toNNReal q) ω - X 0 ω) := by
  funext ω q
  simp only [rationalUniformBlockProcessFromTime,
    rationalUniformBlockAbsoluteTime_zero_eq_horizon]
  simp [RationalCoordinate.toNNReal_bot]

@[simp]
theorem rationalUniformBlockBoundary_succ_one (n : ℕ) :
    rationalUniformBlockBoundary (n + 1) 1 (Nat.succ_pos n) =
      1 / ((n : ℝ≥0) + 1) := by
  apply NNReal.coe_injective
  simp [rationalUniformBlockBoundary, Nat.cast_add]
  rfl

theorem rationalUniformBlockAbsoluteTime_top_eq_bot_of_succ
    {blocks : ℕ} (hblocks : 0 < blocks) (j j' : Fin blocks)
    (hnext : j.val + 1 = j'.val) :
    rationalUniformBlockAbsoluteTime hblocks j ⊤ =
      rationalUniformBlockAbsoluteTime hblocks j' ⊥ := by
  apply NNReal.coe_injective
  change (((((j.val : ℚ) + (1 : ℚ)) / (blocks : ℚ) : ℚ) : ℝ)) =
    (((((j'.val : ℚ) + (0 : ℚ)) / (blocks : ℚ) : ℚ) : ℝ))
  have hnextQ : (j.val : ℚ) + 1 = (j'.val : ℚ) := by exact_mod_cast hnext
  simp [hnextQ]

/-- Elapsed time inside a uniform block. It is independent of the block
index and is the clock used by translated process restrictions. -/
def rationalUniformBlockClock {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑RationalCoordinate.UnitInterval) : ℝ :=
  (rationalUniformBlockAbsoluteTime hblocks j q : ℝ) -
    (rationalUniformBlockAbsoluteTime hblocks j ⊥ : ℝ)

/-- Every uniform block has the same elapsed-time clock `q / blocks`. -/
theorem rationalUniformBlockClock_eq {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (q : ↑RationalCoordinate.UnitInterval) :
    rationalUniformBlockClock hblocks j q =
      (q : ℝ) / (blocks : ℝ) := by
  simp only [rationalUniformBlockClock, rationalUniformBlockAbsoluteTime,
    RationalCoordinate.toNNReal_coe, rationalUniformBlockTime_bot]
  change ((((j.val : ℚ) + (q : ℚ)) / (blocks : ℚ) : ℚ) : ℝ) -
      (((j.val : ℚ) / (blocks : ℚ) : ℚ) : ℝ) =
    (q : ℝ) / (blocks : ℝ)
  push_cast
  field_simp [ne_of_gt hblocks]
  ring

/-- The increment path across one uniform block, read on rational unit time.
The subtraction makes the event depend only on the block increments. -/
def rationalTubeBlockIncrement {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) (x : ↑RationalCoordinate.UnitInterval → ℝ) :
    ↑RationalCoordinate.UnitInterval → ℝ :=
  fun q => x (rationalUniformBlockTime hblocks j q) -
    x (rationalUniformBlockTime hblocks j ⊥)

/-- The event that the increment path on one uniform block has oscillation
strictly less than `width`. -/
def rationalTubeBlockEvent (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks)
    (j : Fin blocks) : Set (↑RationalCoordinate.UnitInterval → ℝ) :=
  (rationalTubeBlockIncrement hblocks j) ⁻¹'
    Skorokhod.rationalCoordinateOscillationTube width

/-- The family of uniform block increment paths cut from a rational-time
process. -/
def rationalUniformBlockProcess {Ω : Type*} (X : ↑RationalCoordinate.UnitInterval →
    Ω → ℝ) {blocks : ℕ} (hblocks : 0 < blocks) :
    Fin blocks → Ω → ↑RationalCoordinate.UnitInterval → ℝ :=
  fun j ω => rationalTubeBlockIncrement hblocks j (fun q => X q ω)

/-- Restricting a measurable rational-time path to a block and subtracting its
initial value is measurable. -/
theorem measurable_rationalTubeBlockIncrement {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    Measurable (rationalTubeBlockIncrement hblocks j) := by
  rw [measurable_pi_iff]
  intro q
  exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- Measurability of all block paths follows from measurability of the
original process as a map into the rational-coordinate path space. -/
theorem measurable_rationalUniformBlockProcess {Ω : Type*}
    [MeasurableSpace Ω]
    (X : ↑RationalCoordinate.UnitInterval → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (hX : Measurable (fun ω q => X q ω)) :
    ∀ j, Measurable (rationalUniformBlockProcess X hblocks j) := by
  intro j
  rw [measurable_pi_iff]
  intro q
  have hEval : ∀ t : ↑RationalCoordinate.UnitInterval,
      Measurable (fun ω => X t ω) := by
    intro t
    exact (measurable_pi_iff.mp hX) t
  exact (hEval _).sub (hEval _)

/-- A block tube is a measurable event in the rational-coordinate path space.
-/
theorem measurableSet_rationalTubeBlockEvent (width : ℝ) {blocks : ℕ}
    (hblocks : 0 < blocks) (j : Fin blocks) :
    MeasurableSet (rationalTubeBlockEvent width hblocks j) :=
  (Skorokhod.measurableSet_rationalCoordinateOscillationTube width).preimage
    (measurable_rationalTubeBlockIncrement hblocks j)

/-- A global rational-coordinate tube gives the same oscillation bound on
every block increment path. This deterministic inclusion is needed for an
upper block bound; only independence remains to turn it into a power of a
one-block probability. -/
theorem rationalCoordinateOscillationTube_subset_iInter_uniformBlockEvents
    (width : ℝ) {blocks : ℕ} (hblocks : 0 < blocks) :
    Skorokhod.rationalCoordinateOscillationTube width ⊆
      ⋂ j : Fin blocks, rationalTubeBlockEvent width hblocks j := by
  intro x hx
  simp only [Set.mem_iInter]
  intro j
  change rationalTubeBlockIncrement hblocks j x ∈
    Skorokhod.rationalCoordinateOscillationTube width
  change ∃ margin : ℚ, 0 < (margin : ℝ) ∧
    ∀ s t : ↑RationalCoordinate.UnitInterval, |x s - x t| ≤ width - margin at hx
  rcases hx with ⟨margin, hmargin, hbound⟩
  refine ⟨margin, hmargin, ?_⟩
  intro s t
  change |(x (rationalUniformBlockTime hblocks j s) -
      x (rationalUniformBlockTime hblocks j 0)) -
    (x (rationalUniformBlockTime hblocks j t) -
      x (rationalUniformBlockTime hblocks j 0))| ≤ width - margin
  rw [show (x (rationalUniformBlockTime hblocks j s) -
      x (rationalUniformBlockTime hblocks j 0)) -
    (x (rationalUniformBlockTime hblocks j t) -
      x (rationalUniformBlockTime hblocks j 0)) =
      x (rationalUniformBlockTime hblocks j s) -
        x (rationalUniformBlockTime hblocks j t) by ring]
  exact hbound _ _

end ProbabilityTheory

end
