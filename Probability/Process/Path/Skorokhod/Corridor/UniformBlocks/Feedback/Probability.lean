/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Independence.Feedback
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Feedback.Basic
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Feedback.FullPath
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.StationaryIncrements.Basic
import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Independence
import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Stationarity

/-!
# Adaptive feedback on a finite uniform path partition

The public theorems specialize the abstract adaptive-choice inequality to
rational paths on uniform blocks. Independent increments make the next block
independent of the stopped prefix; stationary increments give one common
one-block lower bound. The process need not be stable.

* `HasIndepIncrements.measure_feedbackNextBlock_ge_mul` proves
  `q * P(prefix ∈ U) ≤ P((prefix ∈ U ∩ S ∧ next ∈ V₋) ∨
  (prefix ∈ U ∩ Sᶜ ∧ next ∈ V₊))` from independent increments and
  coordinate measurability.
* `HasIndepIncrements.measure_rationalPrefixFiniteChoiceNextBlock_ge_mul`
  proves the finite-choice version: a pairwise disjoint measurable family of
  prefix cells selects measurable next-block events, each with probability
  at least `c`, and the union of successful choices has probability at least
  `c` times the probability of the union of prefix cells.
* `HasIndepIncrements.pow_le_measure_feedbackPrefix` proves
  `q ^ blocks ≤ P(rationalUniformPrefixPath X blocks blocks hblocks ∈
  rationalFeedbackPrefixSet hblocks blocks target V₊ V₋)` when each of the two
  correction events has probability at least `q`.
* `HasIndepIncrements.feedbackPrefix_probability_pos` gives
  the same displayed event positive probability from positive one-block
  correction probabilities.
* `measure_firstBlock_feedbackCorrection_eq_full` identifies the first
  event `{ω | rationalUniformBlockProcessFromTime X ... ω ∈
  feedbackCorrectionSet δ d lower upper}` with
  `fullSegmentCorridorEvent X 0 (1 / (n + 1)) (-δ) δ ∩
  {ω | X (1 / (n + 1)) ω - X 0 ω - d ∈ Set.Ioo lower upper}` in measure.
* `HasIndepIncrements.feedbackPrefix_probability_pos_of_fullBlocks` turns
  positive probabilities for those two complete short-block events into
  positive probability of the complete adaptive block event, assuming
  stationary independent increments and almost-sure càdlàg paths.
* `HasIndepIncrements.linearTube_probability_pos_of_feedbackBlocks` proves
  `P(∀ t ∈ [0,1], |X t - X 0 - v t| < η) > 0` from the two positive
  correction probabilities.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem HasIndepIncrements.measure_feedbackNextBlock_ge_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (U S Vplus Vminus : Set (↑RationalCoordinate.UnitInterval → ℝ))
    (hU : MeasurableSet U) (hS : MeasurableSet S)
    (hVplus : MeasurableSet Vplus) (hVminus : MeasurableSet Vminus)
    (q : ENNReal)
    (hqplus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' Vplus))
    (hqminus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' Vminus)) :
    q * P (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U) ≤
      P (((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' (U ∩ S)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          Vminus)) ∪
        ((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' (U ∩ Sᶜ)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          Vplus))) := by
  let past := rationalUniformPrefixPath X blocks j.val hblocks
  let next : Ω → ↑RationalCoordinate.UnitInterval → ℝ :=
    fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω
  have hpast : AEMeasurable past P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (min (RationalCoordinate.toNNReal q)
        (rationalUniformBlockBoundary blocks j.val hblocks)) ω - X 0 ω) P
    exact (hXmeas _).sub (hXmeas 0)
  have hnext : AEMeasurable next P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (rationalUniformBlockAbsoluteTime hblocks j q) ω -
        X (rationalUniformBlockAbsoluteTime hblocks j ⊥) ω) P
    exact (hXmeas _).sub (hXmeas _)
  exact measure_adaptiveChoice_ge_mul P past next
    (h.indepFun_rationalPrefix_nextBlock hXmeas blocks hblocks j)
    hpast hnext U S Vplus Vminus hU hS hVplus hVminus q hqplus hqminus

/-- A finite disjoint family of admissible prefix cells can select the
next-block event according to the cell containing the prefix. If each selected
event has probability at least `c`, then the probability of a successful
choice is at least `c` times the probability of the union of the prefix cells.
The independent-increment hypothesis is the only process-law assumption. -/
theorem HasIndepIncrements.measure_rationalPrefixFiniteChoiceNextBlock_ge_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (U V : ι → Set (↑RationalCoordinate.UnitInterval → ℝ)) (c : ENNReal)
    (hU : ∀ i, MeasurableSet (U i))
    (hV : ∀ i, MeasurableSet (V i))
    (hdisj : Pairwise (fun i k => Disjoint (U i) (U k)))
    (hc : ∀ i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' V i)) :
    c * P (⋃ i, rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) ≤
      P (⋃ i, (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          V i)) := by
  let past := rationalUniformPrefixPath X blocks j.val hblocks
  let next : Ω → ↑RationalCoordinate.UnitInterval → ℝ :=
    fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω
  have hindep : past ⟂ᵢ[P] next :=
    h.indepFun_rationalPrefix_nextBlock hXmeas blocks hblocks j
  have hpast : AEMeasurable past P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (min (RationalCoordinate.toNNReal q)
        (rationalUniformBlockBoundary blocks j.val hblocks)) ω - X 0 ω) P
    exact (hXmeas _).sub (hXmeas 0)
  have hnext : AEMeasurable next P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (rationalUniformBlockAbsoluteTime hblocks j q) ω -
        X (rationalUniformBlockAbsoluteTime hblocks j ⊥) ω) P
    exact (hXmeas _).sub (hXmeas _)
  exact measure_finiteAdaptiveChoice_ge_mul P past next hindep hpast hnext
    U V c hU hV hdisj hc

/-- The measurable sign rule chooses a negative correction when the endpoint
is nonnegative and a positive correction otherwise. This gives the exact
one-step lower bound used by the finite feedback induction. -/
private theorem HasIndepIncrements.measure_signedFeedbackNextBlock_ge_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (U : Set (↑RationalCoordinate.UnitInterval → ℝ))
    (hU : MeasurableSet U) (target δ d r R : ℝ)
    (q : ENNReal)
    (hqplus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        feedbackCorrectionSet δ d r R))
    (hqminus : q ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        feedbackCorrectionSet δ d (-R) (-r))) :
    q * P (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U) ≤
      P (((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹'
        (U ∩ feedbackPrefixNonnegative target)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          feedbackCorrectionSet δ d (-R) (-r))) ∪
        ((rationalUniformPrefixPath X blocks j.val hblocks ⁻¹'
          (U ∩ (feedbackPrefixNonnegative target)ᶜ)) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
          feedbackCorrectionSet δ d r R))) := by
  exact h.measure_feedbackNextBlock_ge_mul hXmeas blocks hblocks j U
    (feedbackPrefixNonnegative target)
    (feedbackCorrectionSet δ d r R)
    (feedbackCorrectionSet δ d (-R) (-r))
    hU (measurableSet_feedbackPrefixNonnegative target)
    (measurableSet_feedbackCorrectionSet δ d r R)
    (measurableSet_feedbackCorrectionSet δ d (-R) (-r))
    q hqplus hqminus

/-- The actual adaptive success event for a fixed finite partition has
probability at least the product of the uniform one-block lower bound. The
next block is chosen from the sign of the current endpoint error, and the
event depends only on the stopped past. -/
theorem HasIndepIncrements.pow_le_measure_feedbackPrefix
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (target : Fin blocks → ℝ) (δ d r R : ℝ) (q : ENNReal)
    (hqplus : ∀ j : Fin blocks,
      q ≤ P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
        feedbackCorrectionSet δ d r R))
    (hqminus : ∀ j : Fin blocks,
      q ≤ P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
        feedbackCorrectionSet δ d (-R) (-r))) :
    q ^ blocks ≤ P (rationalUniformPrefixPath X blocks blocks hblocks ⁻¹'
      rationalFeedbackPrefixSet hblocks blocks target
        (feedbackCorrectionSet δ d r R)
        (feedbackCorrectionSet δ d (-R) (-r))) := by
  let Vplus := feedbackCorrectionSet δ d r R
  let Vminus := feedbackCorrectionSet δ d (-R) (-r)
  have hbound (m : ℕ) (hm : m ≤ blocks) :
      q ^ m ≤ P (rationalUniformPrefixPath X blocks m hblocks ⁻¹'
        rationalFeedbackPrefixSet hblocks m target Vplus Vminus) := by
    induction m with
    | zero =>
      simp [rationalFeedbackPrefixSet_zero, measure_univ]
    | succ k ih =>
      have hk : k < blocks := by omega
      let j : Fin blocks := ⟨k, hk⟩
      have hchoice := h.measure_signedFeedbackNextBlock_ge_mul hXmeas
        blocks hblocks j
        (rationalFeedbackPrefixSet hblocks k target Vplus Vminus)
        (measurableSet_rationalFeedbackPrefixSet hblocks k target
          (measurableSet_feedbackCorrectionSet δ d r R)
          (measurableSet_feedbackCorrectionSet δ d (-R) (-r)))
        (target j) δ d r R q (hqplus j) (hqminus j)
      have hsubset :
          ((rationalUniformPrefixPath X blocks k hblocks ⁻¹'
              (rationalFeedbackPrefixSet hblocks k target Vplus Vminus ∩
                feedbackPrefixNonnegative (target j))) ∩
              ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
                Vminus)) ∪
            ((rationalUniformPrefixPath X blocks k hblocks ⁻¹'
              (rationalFeedbackPrefixSet hblocks k target Vplus Vminus ∩
                (feedbackPrefixNonnegative (target j))ᶜ)) ∩
              ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
                Vplus)) ⊆
            rationalUniformPrefixPath X blocks (k + 1) hblocks ⁻¹'
              rationalFeedbackPrefixSet hblocks (k + 1) target Vplus Vminus := by
        intro ω hω
        rcases hω with hminus | hplus
        · exact rationalFeedbackPrefixSet_step X hblocks j ω target Vplus Vminus
            hminus.1.1 (Or.inl ⟨hminus.1.2, hminus.2⟩)
        · exact rationalFeedbackPrefixSet_step X hblocks j ω target Vplus Vminus
            hplus.1.1 (Or.inr ⟨lt_of_not_ge hplus.1.2, hplus.2⟩)
      calc
        q ^ (k + 1) = q * q ^ k := pow_succ' q k
        _ ≤ q * P (rationalUniformPrefixPath X blocks k hblocks ⁻¹'
            rationalFeedbackPrefixSet hblocks k target Vplus Vminus) := by
          simpa [mul_comm] using mul_le_mul_left (ih (by omega)) q
        _ ≤ P _ := hchoice
        _ ≤ P (rationalUniformPrefixPath X blocks (k + 1) hblocks ⁻¹'
            rationalFeedbackPrefixSet hblocks (k + 1) target Vplus Vminus) :=
          measure_mono hsubset
  exact hbound blocks le_rfl

/-- Positive probability of the two first-block correction events implies
positive probability for the entire adaptive finite-block success event.
Stationarity supplies the same lower bound at every block. -/
theorem HasIndepIncrements.feedbackPrefix_probability_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (target : Fin blocks → ℝ) (δ d r R : ℝ)
    (hplus : 0 < P ((fun ω s => rationalUniformBlockProcessFromTime
      X hblocks ⟨0, hblocks⟩ s ω) ⁻¹' feedbackCorrectionSet δ d r R))
    (hminus : 0 < P ((fun ω s => rationalUniformBlockProcessFromTime
      X hblocks ⟨0, hblocks⟩ s ω) ⁻¹' feedbackCorrectionSet δ d (-R) (-r))) :
    0 < P (rationalUniformPrefixPath X blocks blocks hblocks ⁻¹'
      rationalFeedbackPrefixSet hblocks blocks target
        (feedbackCorrectionSet δ d r R)
        (feedbackCorrectionSet δ d (-R) (-r))) := by
  let q : ENNReal :=
    min (P ((fun ω s => rationalUniformBlockProcessFromTime
      X hblocks ⟨0, hblocks⟩ s ω) ⁻¹' feedbackCorrectionSet δ d r R))
      (P ((fun ω s => rationalUniformBlockProcessFromTime
        X hblocks ⟨0, hblocks⟩ s ω) ⁻¹'
          feedbackCorrectionSet δ d (-R) (-r)))
  have hq : 0 < q := lt_min hplus hminus
  have hqplus (j : Fin blocks) :
      q ≤ P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
        feedbackCorrectionSet δ d r R) := by
    rw [(h.rationalUniformBlockProcess_identDistrib
      hstationary blocks hblocks j
      ⟨0, hblocks⟩).measure_mem_eq
        (measurableSet_feedbackCorrectionSet δ d r R)]
    exact min_le_left _ _
  have hqminus (j : Fin blocks) :
      q ≤ P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
        feedbackCorrectionSet δ d (-R) (-r)) := by
    rw [(h.rationalUniformBlockProcess_identDistrib
      hstationary blocks hblocks j
      ⟨0, hblocks⟩).measure_mem_eq
        (measurableSet_feedbackCorrectionSet δ d (-R) (-r))]
    exact min_le_right _ _
  exact (ENNReal.pow_pos hq blocks).trans_le
    (h.pow_le_measure_feedbackPrefix hXmeas blocks hblocks target δ d r R q
      hqplus hqminus)

/-- The measurable first-block correction event has the same probability as
its complete càdlàg segment formulation. -/
theorem measure_firstBlock_feedbackCorrection_eq_full
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    (n : ℕ) (δ d lower upper : ℝ) :
    P ((fun ω s => rationalUniformBlockProcessFromTime X
      (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ s ω) ⁻¹'
        feedbackCorrectionSet δ d lower upper) =
      P (fullSegmentCorridorEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) - d ∈
          Set.Ioo lower upper}) := by
  let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  have hfirst := rationalUniformBlockProcess_zero_eq_initial X
    (Nat.succ_pos n)
  rw [rationalUniformBlockBoundary_succ_one] at hfirst
  have heq :
      ((fun ω s => rationalUniformBlockProcessFromTime X
        (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ s ω) ⁻¹'
          feedbackCorrectionSet δ d lower upper) =ᵐ[P]
        (fullSegmentCorridorEvent X 0 t (-δ) δ ∩
          {ω | (X t ω - X 0 ω) - d ∈ Set.Ioo lower upper}) := by
    filter_upwards [hcadlag] with ω hω
    have hcorr := mem_fullSegmentCorridorEvent_iff_rational
      X 0 t (-δ) δ ω hω
    simp only [feedbackCorrectionSet, Set.mem_preimage,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    have hfirstω := congrFun hfirst ω
    have hend : rationalUniformBlockProcessFromTime X
        (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ ⊤ ω = X t ω - X 0 ω := by
      simpa [t, RationalCoordinate.toNNReal_top] using congrFun hfirstω ⊤
    rw [hfirstω]
    rw [hend]
    simp only [zero_add] at *
    exact propext (and_congr hcorr.symm Iff.rfl)
  exact measure_congr heq

/-- Positive complete-path correction probabilities for one short block
imply positive probability of all adaptively chosen blocks. -/
theorem HasIndepIncrements.feedbackPrefix_probability_pos_of_fullBlocks
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    (n : ℕ) (target : Fin (n + 1) → ℝ) (δ d r R : ℝ)
    (hplus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) - d ∈ Set.Ioo r R}))
    (hminus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) - d ∈ Set.Ioo (-R) (-r)})) :
    0 < P (rationalUniformPrefixPath X (n + 1) (n + 1)
      (Nat.succ_pos n) ⁻¹'
        rationalFeedbackPrefixSet (Nat.succ_pos n) (n + 1) target
          (feedbackCorrectionSet δ d r R)
          (feedbackCorrectionSet δ d (-R) (-r))) := by
  have hplus' : 0 < P ((fun ω s => rationalUniformBlockProcessFromTime
      X (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ s ω) ⁻¹'
        feedbackCorrectionSet δ d r R) := by
    rw [measure_firstBlock_feedbackCorrection_eq_full hcadlag]
    exact hplus
  have hminus' : 0 < P ((fun ω s => rationalUniformBlockProcessFromTime
      X (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ s ω) ⁻¹'
        feedbackCorrectionSet δ d (-R) (-r)) := by
    rw [measure_firstBlock_feedbackCorrection_eq_full hcadlag]
    exact hminus
  exact h.feedbackPrefix_probability_pos hstationary hXmeas
    (n + 1) (Nat.succ_pos n)
    target δ d r R hplus' hminus'

/-- Positive probability of the two one-block correction events gives
positive probability for a complete path to stay in a tube around a linear
function, after centering the process at its initial value. The assumptions
are independent and stationary increments, coordinate measurability, and
almost-sure càdlàg paths. -/
theorem HasIndepIncrements.linearTube_probability_pos_of_feedbackBlocks
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    (n : ℕ) (v δ r R η : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hwidth : 2 * (R + δ + |v / ((n : ℝ) + 1)|) < η)
    (hplus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) -
        v / ((n : ℝ) + 1) ∈ Set.Ioo r R}))
    (hminus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) -
        v / ((n : ℝ) + 1) ∈ Set.Ioo (-R) (-r)})) :
    0 < P {ω | ∀ t : unitInterval,
      |X (UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ)| < η} := by
  let success : Set Ω :=
    rationalUniformPrefixPath X (n + 1) (n + 1) (Nat.succ_pos n) ⁻¹'
      rationalFeedbackPrefixSet (Nat.succ_pos n) (n + 1)
        (fun j => v * (j.val : ℝ) / ((n : ℝ) + 1))
        (feedbackCorrectionSet δ (v / ((n : ℝ) + 1)) r R)
        (feedbackCorrectionSet δ (v / ((n : ℝ) + 1)) (-R) (-r))
  have hsuccess : 0 < P success := by
    simpa [success, Nat.cast_add] using
      h.feedbackPrefix_probability_pos_of_fullBlocks hstationary hXmeas
        hcadlag n
        (fun j => v * (j.val : ℝ) / ((n : ℝ) + 1))
        δ (v / ((n : ℝ) + 1)) r R hplus hminus
  have hcongr : success =ᵐ[P]
      {ω | ∀ t : unitInterval,
        |X (UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ)| < η} ∩ success := by
    filter_upwards [hcadlag] with ω hω
    apply propext
    constructor
    · intro hs
      refine ⟨?_, hs⟩
      exact rationalFeedback_fullPath_bound X ω hω
        (Nat.succ_pos n) v δ r R η hr hR
        (by simpa [Nat.cast_add] using hwidth)
        (by simpa [success, Nat.cast_add] using hs)
    · exact And.right
  rw [measure_congr hcongr] at hsuccess
  exact hsuccess.trans_le (measure_mono Set.inter_subset_left)

end ProbabilityTheory

end
