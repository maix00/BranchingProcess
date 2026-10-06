/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalGrid.UnitInterval
public import Probability.Process.Stable.SmallDeviation.Blocks.Factorization
public import Probability.Independence.FinitePartition

/-!
# Finite endpoint bins for a stable-process block

The prefix path determines a finite endpoint bin, while the next block path
is independent of that choice. The next-block event is allowed to depend on
the bin. This is the probability step in the lower block argument of the
original Mogulskii proof.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_prefixBin_nextBlock_ge_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (U V : ι → Set (↑RationalGrid.UnitCoordinate → ℝ)) (c : ENNReal)
    (hU : ∀ i, MeasurableSet (U i))
    (hV : ∀ i, MeasurableSet (V i))
    (hdisj : Pairwise (fun i k => Disjoint (U i) (U k)))
    (hc : ∀ i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' V i)) :
    c * P (⋃ i, rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) ≤
      P (⋃ i, (rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' V i)) := by
  let past := rationalUniformPrefixPath X blocks j.val hblocks
  let next : Ω → ↑RationalGrid.UnitCoordinate → ℝ :=
    fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω
  have hindep : past ⟂ᵢ[P] next := h.indepFun_rationalPrefix_nextBlock blocks hblocks j
  have hpast : AEMeasurable past P := by
    rw [aemeasurable_pi_iff]
    intro q
    change AEMeasurable (fun ω =>
      X (min (rationalUnitTime q)
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
  apply measure_iUnion_inter_ge_mul_of_finite_partition P
    (fun i => past ⁻¹' U i) (fun i => next ⁻¹' V i) c
  · exact fun i => hpast.nullMeasurableSet_preimage (hU i)
  · exact fun i => hnext.nullMeasurableSet_preimage (hV i)
  · intro i k hik
    exact (hdisj hik).preimage past
  · intro i
    exact hindep.measure_inter_preimage_eq_mul (U i) (V i) (hU i) (hV i)
  · exact hc

/-- If finitely many disjoint endpoint bins cover every admissible prefix
endpoint, the full prefix event can be used on the left side of the lower
bound. The next-block constraint may be different in every bin. -/
theorem IsStableLevyProcess.measure_prefixTube_nextBlock_bins_ge_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks)
    (width : ℝ) (I : ι → Set ℝ)
    (V : ι → Set (↑RationalGrid.UnitCoordinate → ℝ)) (c : ENNReal)
    (hI : ∀ i, MeasurableSet (I i))
    (hV : ∀ i, MeasurableSet (V i))
    (hdisj : Pairwise (fun i k => Disjoint (I i) (I k)))
    (hcover : ∀ ω ∈ rationalUniformPrefixTubeEvent X width hblocks j.val,
      ∃ i, rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I i)
    (hc : ∀ i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' V i)) :
    c * P (rationalUniformPrefixTubeEvent X width hblocks j.val) ≤
      P (⋃ i, (rationalUniformPrefixTubeEvent X width hblocks j.val ∩
        {ω | rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I i}) ∩
        ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹' V i)) := by
  let U : ι → Set (↑RationalGrid.UnitCoordinate → ℝ) :=
    fun i => rationalUniformPrefixTubeSet width hblocks j.val ∩
      {x | x ⊤ ∈ I i}
  have hU : ∀ i, MeasurableSet (U i) := by
    intro i
    exact (measurableSet_rationalUniformPrefixTubeSet width hblocks j.val).inter
      ((hI i).preimage (measurable_pi_apply ⊤))
  have hUdisj : Pairwise (fun i k => Disjoint (U i) (U k)) := by
    intro i k hik
    apply Set.disjoint_left.mpr
    intro x hxi hxk
    exact Set.disjoint_left.mp (hdisj hik) hxi.2 hxk.2
  have hunion :
      (⋃ i, rationalUniformPrefixPath X blocks j.val hblocks ⁻¹' U i) =
        rationalUniformPrefixTubeEvent X width hblocks j.val := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_preimage, U,
      rationalUniformPrefixTubeEvent_eq_preimage]
    constructor
    · rintro ⟨i, hprefix, _⟩
      exact hprefix
    · intro hprefix
      have hprefixEvent : ω ∈ rationalUniformPrefixTubeEvent X width hblocks j.val := by
        rw [rationalUniformPrefixTubeEvent_eq_preimage]
        exact hprefix
      obtain ⟨i, hi⟩ := hcover ω hprefixEvent
      exact ⟨i, hprefix, hi⟩
  have hbound := h.measure_prefixBin_nextBlock_ge_mul blocks hblocks j U V c
    hU hV hUdisj hc
  rw [hunion] at hbound
  simpa only [U, Set.preimage_inter, Set.preimage_ofPred_eq,
    rationalUniformPrefixTubeEvent_eq_preimage] using hbound

end ProbabilityTheory
