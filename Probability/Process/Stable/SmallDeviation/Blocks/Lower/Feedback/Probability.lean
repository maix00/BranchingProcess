/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Stable.SmallDeviation.Blocks.Factorization
public import Probability.Independence.Feedback
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Feedback
public import Probability.Process.Path.Skorokhod.Corridor.Segment

/-!
# Feedback choice for the next stable-process block

A condition on the complete stopped prefix path may select either of two
conditions on the next complete block path. The resulting probability bound
does not assume that the selected event itself is independent of the past.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_feedbackNextBlock_ge_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
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
    exact (h.increments.aemeasurable_eval _).sub
      (h.increments.aemeasurable_eval 0)
  have hnext : AEMeasurable next P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (rationalUniformBlockAbsoluteTime hblocks j q) ω -
        X (rationalUniformBlockAbsoluteTime hblocks j ⊥) ω) P
    exact (h.increments.aemeasurable_eval _).sub
      (h.increments.aemeasurable_eval _)
  exact measure_adaptiveChoice_ge_mul P past next
    (h.indepFun_rationalPrefix_nextBlock blocks hblocks j)
    hpast hnext U S Vplus Vminus hU hS hVplus hVminus q hqplus hqminus

/-- The measurable sign rule chooses a negative correction when the endpoint
is nonnegative and a positive correction otherwise. This gives the exact
one-step lower bound used by the finite feedback induction. -/
theorem IsStableLevyProcess.measure_signedFeedbackNextBlock_ge_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
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
  exact h.measure_feedbackNextBlock_ge_mul blocks hblocks j U
    (feedbackPrefixNonnegative target)
    (feedbackCorrectionSet δ d r R)
    (feedbackCorrectionSet δ d (-R) (-r))
    hU (measurableSet_feedbackPrefixNonnegative target)
    (measurableSet_feedbackCorrectionSet δ d r R)
    (measurableSet_feedbackCorrectionSet δ d (-R) (-r))
    q hqplus hqminus

/-- The actual adaptive success event for a fixed finite stable-process
partition has probability at least the product of the uniform one-block
lower bound. The next block is chosen from the sign of the current endpoint
error, and the event depends only on the stopped past. -/
theorem IsStableLevyProcess.pow_le_measure_feedbackPrefix
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
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
      have hchoice := h.measure_signedFeedbackNextBlock_ge_mul
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
theorem IsStableLevyProcess.feedbackPrefix_probability_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
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
    rw [(h.rationalUniformBlockProcess_identDistrib blocks hblocks j
      ⟨0, hblocks⟩).measure_mem_eq
        (measurableSet_feedbackCorrectionSet δ d r R)]
    exact min_le_left _ _
  have hqminus (j : Fin blocks) :
      q ≤ P ((fun ω s => rationalUniformBlockProcessFromTime X hblocks j s ω) ⁻¹'
        feedbackCorrectionSet δ d (-R) (-r)) := by
    rw [(h.rationalUniformBlockProcess_identDistrib blocks hblocks j
      ⟨0, hblocks⟩).measure_mem_eq
        (measurableSet_feedbackCorrectionSet δ d (-R) (-r))]
    exact min_le_right _ _
  exact (ENNReal.pow_pos hq blocks).trans_le
    (h.pow_le_measure_feedbackPrefix blocks hblocks target δ d r R q
      hqplus hqminus)

/-- The measurable first-block correction event has the same probability as
its complete càdlàg segment formulation. -/
theorem IsStableLevyProcess.measure_firstBlock_feedbackCorrection_eq_full
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
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
    filter_upwards [h.ae_cadlag] with ω hω
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
theorem IsStableLevyProcess.feedbackPrefix_probability_pos_of_fullBlocks
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
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
    rw [h.measure_firstBlock_feedbackCorrection_eq_full]
    exact hplus
  have hminus' : 0 < P ((fun ω s => rationalUniformBlockProcessFromTime
      X (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ s ω) ⁻¹'
        feedbackCorrectionSet δ d (-R) (-r)) := by
    rw [h.measure_firstBlock_feedbackCorrection_eq_full]
    exact hminus
  exact h.feedbackPrefix_probability_pos (n + 1) (Nat.succ_pos n)
    target δ d r R hplus' hminus'

end ProbabilityTheory

end
