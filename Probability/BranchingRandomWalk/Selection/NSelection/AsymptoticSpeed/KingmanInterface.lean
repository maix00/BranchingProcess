/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.ErgodicEnvironment
public import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
public import Probability.BranchingRandomWalk.Selection.NSelection.Totalized
public import Probability.BranchingRandomWalk.Assumptions.Moments
public import Probability.BranchingRandomWalk.Step.Ordering.Law
public import Probability.Ergodic.Kingman.Core
public import Combinatorics.BranchingWalk.Selection.NSelection.Speed
public import Combinatorics.BranchingWalk.Step.Map
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.IdentDistrib

/-!
# Measurable Kingman input for the countable-offspring selection process

This module develops a measurable, totalized realization of the actual
optional-slot selection dynamics. Bad generation batches are repaired to a
fixed valid batch; under the branching assumptions this modification is
almost surely invisible, while it makes the deterministic cocycle laws hold
for every environment.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

instance (N : ℕ) : Countable (InfiniteSlotLabel N) := by
  unfold InfiniteSlotLabel
  exact Countable.of_equiv (Fin N × ℕ) toLex

instance (N : ℕ) : MeasurableSpace (InfiniteSlotLabel N) := ⊤

instance (N : ℕ) : MeasurableSingletonClass (InfiniteSlotLabel N) :=
  ⟨fun _ => trivial⟩

/-! ## Measurable validity and repair -/

/-- A canonical batch with one child per parent, at displacement zero. -/
def fallbackOffspringStep : Step ℕ ℝ := fun j => if j = 0 then some 0 else none

theorem fallbackOffspringStep_totalChildWeight :
    totalChildWeight fallbackOffspringStep = 1 := by
  classical
  unfold totalChildWeight
  rw [tsum_eq_single 0]
  · simp [realizedChildWeight, fallbackOffspringStep, survive, value']
  · intro j hj
    simp [realizedChildWeight, fallbackOffspringStep, survive, hj]

/-- A batch is valid for the selection recursion if each parent has finite
negative exponential weight and at least one child. -/
def IsRepairableBatch {N : ℕ} (batch : GenerationBatch N) : Prop :=
  IsGoodInfiniteOffspringBatch batch

private theorem infiniteOffspringCandidate_mem_measurable {N : ℕ}
    (q : InfiniteSlotLabel N) :
    Measurable fun batch : GenerationBatch N =>
      q ∈ infiniteOffspringCandidates batch := by
  apply measurableSet_setOfPred.mp
  change MeasurableSet
    {batch : GenerationBatch N |
      survive (batch (ofLex q).1) (ofLex q).2}
  exact (survive_measurableSet (ofLex q).2).preimage
    (measurable_pi_apply (ofLex q).1)

private theorem measurable_infiniteOffspringCandidates {N : ℕ} :
    Measurable (fun batch : GenerationBatch N =>
      infiniteOffspringCandidates batch) := by
  rw [measurable_set_iff]
  intro q
  exact infiniteOffspringCandidate_mem_measurable q

/-- The complete candidate-position family is measurable in both the
ranked input configuration and the generation batch. -/
theorem measurable_infiniteOffspringPosition {N : ℕ} :
    Measurable (fun x : (Fin N → ℝ) × GenerationBatch N =>
      infiniteOffspringPosition x.1 x.2) := by
  apply Measurable.of_eval
  intro q
  dsimp [infiniteOffspringPosition]
  have hparent : Measurable (fun x : (Fin N → ℝ) × GenerationBatch N =>
      x.2 (ofLex q).1) :=
    (measurable_pi_apply (ofLex q).1).comp measurable_snd
  exact ((measurable_pi_apply (ofLex q).1).comp measurable_fst).add
    ((value'_measurable (ofLex q).2).comp hparent)

/-- A measurable totalized first-`N` selector for the actual countable-slot
offspring model. -/
noncomputable def totalizedInfiniteOffspringFirstN {N : ℕ}
    (x : (Fin N → ℝ) × GenerationBatch N) :
    Finset (InfiniteSlotLabel N) :=
  selectFirstNFromSetTotalized N
    (fun y => infiniteOffspringPosition y.1 y.2)
    (fun y => infiniteOffspringCandidates y.2) x

theorem measurable_totalizedInfiniteOffspringFirstN {N : ℕ} :
    Measurable (totalizedInfiniteOffspringFirstN (N := N)) := by
  apply measurable_selectFirstNFromSetTotalized
  · exact measurable_infiniteOffspringCandidates.comp measurable_snd
  · intro p q
    apply NSelection.measurable_valueKey_lt
    intro r
    exact Measurable.eval (a := r)
      (measurable_infiniteOffspringPosition (N := N))

/-- On a repairable batch the measurable totalization agrees with the
mathematical first-`N` segment used by the deterministic transition. -/
theorem totalizedInfiniteOffspringFirstN_eq_infiniteOffspringFirstN
    {N : ℕ} (position : Fin N → ℝ) (batch : GenerationBatch N)
    (hgood : IsGoodInfiniteOffspringBatch batch) :
    totalizedInfiniteOffspringFirstN (position, batch) =
      infiniteOffspringFirstN position batch hgood.finiteWeight := by
  have hlower := infiniteOffspringCandidates_lowerFinite position batch
    hgood.finiteWeight
  simp [totalizedInfiniteOffspringFirstN, selectFirstNFromSetTotalized,
    hlower, infiniteOffspringFirstN]

/-- The rank lookup is kept option-valued on arbitrary input data, since the
totalized first-`N` set may have fewer than `N` members. -/
noncomputable def totalizedInfiniteOffspringRankOption {N : ℕ}
    (x : (Fin N → ℝ) × GenerationBatch N) (i : Fin N) :
    Option (InfiniteSlotLabel N) :=
  particleAtRankBy (infiniteOffspringPosition x.1 x.2)
    (totalizedInfiniteOffspringFirstN x) i.val

private theorem measurable_totalizedInfiniteOffspringRankOption_eq_some
    {N : ℕ} (i : Fin N) (q : InfiniteSlotLabel N) :
    MeasurableSet {x : (Fin N → ℝ) × GenerationBatch N |
      totalizedInfiniteOffspringRankOption x i = some q} := by
  let value : (Fin N → ℝ) × GenerationBatch N → InfiniteSlotLabel N → ℝ :=
    fun x => infiniteOffspringPosition x.1 x.2
  let selected : (Fin N → ℝ) × GenerationBatch N →
      Finset (InfiniteSlotLabel N) := totalizedInfiniteOffspringFirstN
  have hfiber : ∀ s, MeasurableSet {x | selected x = s} := by
    intro s
    exact measurable_totalizedInfiniteOffspringFirstN
      (measurableSet_singleton s)
  have hkey : ∀ p r : InfiniteSlotLabel N, Measurable fun x =>
      valueKey (value x) r < valueKey (value x) p := by
    intro p r
    apply NSelection.measurable_valueKey_lt
    intro t
    exact Measurable.eval (a := t)
      (measurable_infiniteOffspringPosition (N := N))
  change MeasurableSet
    {x | particleAtRankBy (value x) (selected x) i.val = some q}
  exact NSelection.measurableSet_particleAtRankBy_eq_some value selected
    hfiber (Set.to_countable _) hkey i.val q

private theorem measurable_totalizedInfiniteOffspringRankOption_eq_none
    {N : ℕ} (i : Fin N) :
    MeasurableSet {x : (Fin N → ℝ) × GenerationBatch N |
      totalizedInfiniteOffspringRankOption x i = none} := by
  let value : (Fin N → ℝ) × GenerationBatch N → InfiniteSlotLabel N → ℝ :=
    fun x => infiniteOffspringPosition x.1 x.2
  let selected : (Fin N → ℝ) × GenerationBatch N →
      Finset (InfiniteSlotLabel N) := totalizedInfiniteOffspringFirstN
  have hfiber : ∀ s, MeasurableSet {x | selected x = s} := by
    intro s
    exact measurable_totalizedInfiniteOffspringFirstN
      (measurableSet_singleton s)
  have hkey : ∀ p r : InfiniteSlotLabel N, Measurable fun x =>
      valueKey (value x) r < valueKey (value x) p := by
    intro p r
    apply NSelection.measurable_valueKey_lt
    intro t
    exact Measurable.eval (a := t)
      (measurable_infiniteOffspringPosition (N := N))
  change MeasurableSet
    {x | particleAtRankBy (value x) (selected x) i.val = none}
  exact NSelection.measurableSet_particleAtRankBy_eq_none value selected
    hfiber (Set.to_countable _) i.val

/-- For a fixed rank, turn a possibly missing rank lookup into a label by
using that parent's zero-mark slot as a deterministic default. -/
noncomputable def totalizedInfiniteOffspringRankLabel {N : ℕ}
    (x : (Fin N → ℝ) × GenerationBatch N) (i : Fin N) :
    InfiniteSlotLabel N :=
  (totalizedInfiniteOffspringRankOption x i).getD (toLex (i, 0))

theorem measurable_totalizedInfiniteOffspringRankLabel {N : ℕ}
    (i : Fin N) :
    Measurable (fun x : (Fin N → ℝ) × GenerationBatch N =>
      totalizedInfiniteOffspringRankLabel x i) := by
  apply measurable_to_countable'
  intro q
  by_cases hq : q = toLex (i, 0)
  · have hset :
        {x : (Fin N → ℝ) × GenerationBatch N |
          totalizedInfiniteOffspringRankLabel x i = q} =
          {x | totalizedInfiniteOffspringRankOption x i = none} ∪
            {x | totalizedInfiniteOffspringRankOption x i = some q} := by
      ext x
      cases h : totalizedInfiniteOffspringRankOption x i <;>
        simp [totalizedInfiniteOffspringRankLabel, h, hq]
    change MeasurableSet
      {x : (Fin N → ℝ) × GenerationBatch N |
        totalizedInfiniteOffspringRankLabel x i = q}
    rw [hset]
    exact (measurable_totalizedInfiniteOffspringRankOption_eq_none i).union
      (measurable_totalizedInfiniteOffspringRankOption_eq_some i q)
  · have hset :
        {x : (Fin N → ℝ) × GenerationBatch N |
          totalizedInfiniteOffspringRankLabel x i = q} =
          {x | totalizedInfiniteOffspringRankOption x i = some q} := by
      ext x
      cases h : totalizedInfiniteOffspringRankOption x i <;>
        simp [totalizedInfiniteOffspringRankLabel, h, Ne.symm hq]
    change MeasurableSet
      {x : (Fin N → ℝ) × GenerationBatch N |
        totalizedInfiniteOffspringRankLabel x i = q}
    rw [hset]
    exact measurable_totalizedInfiniteOffspringRankOption_eq_some i q

/-- A totalized measurable one-generation transition. On repaired batches
its candidate set has exactly `N` entries, so no default rank is used. -/
noncomputable def totalizedInfiniteOffspringTransition {N : ℕ}
    (x : (Fin N → ℝ) × GenerationBatch N) : Fin N → ℝ :=
  fun i => infiniteOffspringPosition x.1 x.2
    (totalizedInfiniteOffspringRankLabel x i)

theorem measurable_totalizedInfiniteOffspringTransition {N : ℕ} :
    Measurable (totalizedInfiniteOffspringTransition (N := N)) := by
  apply Measurable.of_eval
  intro i
  let hpos := measurable_infiniteOffspringPosition (N := N)
  have hjoint : Measurable
      (fun y : ((Fin N → ℝ) × GenerationBatch N) × InfiniteSlotLabel N =>
        infiniteOffspringPosition y.1.1 y.1.2 y.2) := by
    apply measurable_from_prod_countable_left
    intro q
    exact Measurable.eval (a := q) hpos
  have hmap : Measurable fun x : (Fin N → ℝ) × GenerationBatch N =>
      (x, totalizedInfiniteOffspringRankLabel x i) :=
    Measurable.prodMk measurable_id
      (measurable_totalizedInfiniteOffspringRankLabel i)
  exact hjoint.comp hmap

/-- On a repairable batch, the measurable totalized transition is exactly the
ranked transition used in the deterministic subadditive argument. -/
theorem totalizedInfiniteOffspringTransition_eq_of_good {N : ℕ}
    (position : Fin N → ℝ) (batch : GenerationBatch N)
    (hgood : IsGoodInfiniteOffspringBatch batch) :
    totalizedInfiniteOffspringTransition (position, batch) =
      infiniteOffspringTransition position batch hgood := by
  classical
  let value := infiniteOffspringPosition position batch
  let selected := infiniteOffspringFirstN position batch hgood.finiteWeight
  have hselected :
      totalizedInfiniteOffspringFirstN (position, batch) = selected :=
    totalizedInfiniteOffspringFirstN_eq_infiniteOffspringFirstN
      position batch hgood
  have hcard : selected.card = N :=
    infiniteOffspringFirstN_card position batch hgood
  have hlabel (i : Fin N) :
      totalizedInfiniteOffspringRankLabel (position, batch) i =
        selectedLabelAtRank value selected hcard i := by
    have hrank : particleAtRankBy value selected i.val =
        some (selectedLabelAtRank value selected hcard i) := by
      exact (Option.some_get _).symm
    unfold totalizedInfiniteOffspringRankLabel totalizedInfiniteOffspringRankOption
    change (particleAtRankBy value
      (totalizedInfiniteOffspringFirstN (position, batch)) i.val).getD _ = _
    rw [hselected, hrank]
    rfl
  ext i
  change infiniteOffspringPosition position batch
      (totalizedInfiniteOffspringRankLabel (position, batch) i) =
    infiniteOffspringPosition position batch
      (selectedLabelAtRank value selected hcard i)
  rw [hlabel i]

theorem isRepairableBatch_measurable {N : ℕ} :
    MeasurableSet {batch : GenerationBatch N | IsRepairableBatch batch} := by
  have hset : {batch : GenerationBatch N | IsRepairableBatch batch} =
      {batch : GenerationBatch N |
        (∀ i, totalChildWeight (batch i) ≠ ∞) ∧
          ∃ s : Finset (InfiniteSlotLabel N),
            (↑s : Set (InfiniteSlotLabel N)) ⊆
              infiniteOffspringCandidates batch ∧ s.card = N} := by
    ext batch
    constructor
    · intro h
      exact ⟨h.finiteWeight, h.enoughCandidates⟩
    · rintro ⟨hw, hs⟩
      exact ⟨hw, hs⟩
  rw [hset]
  apply MeasurableSet.inter
  · change MeasurableSet
      {batch : GenerationBatch N |
        ∀ i : Fin N, totalChildWeight (batch i) ≠ ∞}
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => by
      have heval : Measurable (fun batch : GenerationBatch N => batch i) :=
        measurable_pi_apply i
      have h : Measurable
          (fun batch : GenerationBatch N => totalChildWeight (batch i)) :=
        totalChildWeight_measurable.comp heval
      have hnotTop : MeasurableSet {x : ℝ≥0∞ | x ≠ ∞} :=
        (measurableSet_singleton ∞).compl
      exact h hnotTop
  · have hset :
        {batch : GenerationBatch N |
          ∃ s : Finset (InfiniteSlotLabel N),
            (↑s : Set (InfiniteSlotLabel N)) ⊆
              infiniteOffspringCandidates batch ∧ s.card = N} =
          ⋃ s : Finset (InfiniteSlotLabel N),
            {batch : GenerationBatch N |
              (↑s : Set (InfiniteSlotLabel N)) ⊆
                infiniteOffspringCandidates batch ∧ s.card = N} := by
      ext batch
      simp
    change MeasurableSet
      {batch : GenerationBatch N |
        ∃ s : Finset (InfiniteSlotLabel N),
          (↑s : Set (InfiniteSlotLabel N)) ⊆
            infiniteOffspringCandidates batch ∧ s.card = N}
    rw [hset]
    exact MeasurableSet.iUnion fun s => by
      by_cases hcard : s.card = N
      · have hEq :
            {batch : GenerationBatch N |
              (↑s : Set (InfiniteSlotLabel N)) ⊆
                infiniteOffspringCandidates batch ∧ s.card = N} =
            {batch : GenerationBatch N |
              (↑s : Set (InfiniteSlotLabel N)) ⊆
                infiniteOffspringCandidates batch} := by
          ext batch
          simp [hcard]
        rw [hEq]
        have hsubset :
              {batch : GenerationBatch N |
                (↑s : Set (InfiniteSlotLabel N)) ⊆
                  infiniteOffspringCandidates batch} =
                ⋂ q ∈ s, {batch : GenerationBatch N |
                  q ∈ infiniteOffspringCandidates batch} := by
            ext batch
            simp only [Set.mem_iInter, Finset.mem_coe, Set.mem_ofPred_eq,
              Set.subset_def]
        rw [hsubset]
        apply MeasurableSet.iInter
        intro q
        apply MeasurableSet.iInter
        intro hq
        exact measurableSet_setOfPred.mpr
          (infiniteOffspringCandidate_mem_measurable q)
      · simp [hcard]

/-- A fixed valid batch: every parent has the canonical one-child step. -/
def fallbackGenerationBatch (N : ℕ) : GenerationBatch N := fun _ => fallbackOffspringStep

theorem fallbackGenerationBatch_repairable (N : ℕ) :
    IsRepairableBatch (fallbackGenerationBatch N) := by
  refine ⟨?_, ?_⟩
  · intro i
    rw [fallbackGenerationBatch, fallbackOffspringStep_totalChildWeight]
    exact ENNReal.one_ne_top
  · apply infiniteOffspringCandidates_hasFiniteSubset_card
    intro i
    refine ⟨0, ?_⟩
    simp [fallbackGenerationBatch, fallbackOffspringStep, survive]

/-- Replace an invalid batch with a deterministic valid batch. -/
noncomputable def repairGenerationBatch {N : ℕ} (batch : GenerationBatch N) :
    GenerationBatch N :=
  by
    classical
    exact if IsRepairableBatch batch then batch else fallbackGenerationBatch N

theorem repairGenerationBatch_repairable {N : ℕ} (batch : GenerationBatch N) :
    IsRepairableBatch (repairGenerationBatch batch) := by
  classical
  by_cases h : IsRepairableBatch batch
  · simp [repairGenerationBatch, h]
  · simpa [repairGenerationBatch, h] using fallbackGenerationBatch_repairable N

theorem repairGenerationBatch_eq_of_repairable {N : ℕ}
    (batch : GenerationBatch N) (h : IsRepairableBatch batch) :
    repairGenerationBatch batch = batch := by
  simp [repairGenerationBatch, h]

private theorem fallbackOffspringStep_isOrderedBy :
    fallbackOffspringStep.IsOrderedBy realPotential := by
  change (fallbackOffspringStep.map id) ∈ orderedSteps
  rw [mem_orderedSteps_iff]
  constructor
  · intro i j hij hi
    by_cases hi0 : i = 0
    · simp [fallbackOffspringStep, hi0] at hi
    · have hj0 : j ≠ 0 := by omega
      simp [Step.map, fallbackOffspringStep, hj0]
  · intro i j x y hij hi hj
    have hix : i = 0 ∧ (0 : ℝ) = x := by
      simpa [Step.map, fallbackOffspringStep] using hi
    have hjy : j = 0 ∧ (0 : ℝ) = y := by
      simpa [Step.map, fallbackOffspringStep] using hj
    have hi0 : i = 0 := hix.1
    have hj0 : j = 0 := hjy.1
    omega

private theorem fallbackGenerationBatch_orderedFirst {N : ℕ} :
    ∀ i : Fin N,
      (fallbackGenerationBatch N i).IsOrderedBy realPotential ∧
        survive (fallbackGenerationBatch N i) 0 := by
  intro i
  constructor
  · exact fallbackOffspringStep_isOrderedBy
  · simp [fallbackGenerationBatch, fallbackOffspringStep, survive]

/-- Repair preserves the ordered leftmost-child property: valid batches are
kept, and invalid batches are replaced by the canonical one-child batch. -/
theorem repairGenerationBatch_orderedFirst_of_orderedFirst {N : ℕ}
    (batch : GenerationBatch N)
    (h : ∀ i : Fin N,
      (batch i).IsOrderedBy realPotential ∧ survive (batch i) 0) :
    ∀ i : Fin N,
      (repairGenerationBatch batch i).IsOrderedBy realPotential ∧
        survive (repairGenerationBatch batch i) 0 := by
  classical
  by_cases hgood : IsRepairableBatch batch
  · simpa [repairGenerationBatch_eq_of_repairable batch hgood] using h
  · simpa [repairGenerationBatch, hgood] using
      (fallbackGenerationBatch_orderedFirst (N := N))

/-- An ordered, nonempty offspring law has a surviving slot-zero child almost
surely. This is transferred through the independent parent coordinates and
then through the generation environment. -/
theorem generationEnvironmentLaw_ae_allOrderedFirst
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hordered : μ (orderedBySteps realPotential) = 1)
    (hnonempty : μ nonemptySupport = 1) (N : ℕ) :
    ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∀ t i, (ω t i).IsOrderedBy realPotential ∧ survive (ω t i) 0 := by
  have horderedAE : ∀ᵐ ξ ∂μ, ξ ∈ orderedBySteps realPotential := by
    exact (ae_mem_iff_measure_eq
      (orderedBySteps_measurable (ι := ℕ) realPotential).nullMeasurableSet).2
        (by simpa using hordered)
  have hnonemptyAE : ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
    exact (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
      (by simpa using hnonempty)
  have hstepAE : ∀ᵐ ξ ∂μ,
      ξ.IsOrderedBy realPotential ∧ survive ξ 0 := by
    filter_upwards [horderedAE, hnonemptyAE] with ξ ho hn
    have hmapOrdered : (ξ.map realPotential) ∈ orderedSteps := ho
    obtain ⟨j, hj⟩ := hn
    have hjmap : survive (ξ.map realPotential) j :=
      (survive_map_iff realPotential ξ j).2 hj
    have hzeroMap : survive (ξ.map realPotential) 0 :=
      orderedSteps_survive_of_le (ξ.map realPotential) hmapOrdered (Nat.zero_le j) hjmap
    exact ⟨ho, (survive_map_iff realPotential ξ 0).1 hzeroMap⟩
  have hbatchAE : ∀ᵐ batch ∂generationBatchLaw μ N,
      ∀ i, (batch i).IsOrderedBy realPotential ∧ survive (batch i) 0 := by
    apply ae_all_iff.2
    intro i
    have hmapAE : ∀ᵐ ξ ∂(generationBatchLaw μ N).map (fun batch => batch i),
        ξ.IsOrderedBy realPotential ∧ survive ξ 0 := by
      rw [generationBatchLaw_parent_marginal μ i]
      exact hstepAE
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hmapAE
  apply ae_all_iff.2
  intro t
  have hmapAE : ∀ᵐ batch ∂(generationEnvironmentLaw μ N).map (fun ω => ω t),
      ∀ i, (batch i).IsOrderedBy realPotential ∧ survive (batch i) 0 := by
    rw [generationEnvironmentLaw_generation_marginal μ N t]
    exact hbatchAE
  exact ae_of_ae_map (measurable_pi_apply t).aemeasurable hmapAE

/-- The one-generation leftmost-child envelope is a measurable real random
variable on the product batch space. -/
theorem measurable_infiniteOffspringBatchSlotZeroNorm {N : ℕ} (hN : 0 < N) :
    Measurable (infiniteOffspringBatchSlotZeroNorm hN : GenerationBatch N → ℝ) := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  let f : Fin N → GenerationBatch N → ℝ := fun i batch => |value' (batch i) 0|
  have hcoord (i : Fin N) :
      Measurable (f i) := by
    apply Measurable.abs
    exact (value'_measurable 0).comp (measurable_pi_apply i)
  have hsup := Finset.measurable_sup' hne (fun i hi => hcoord i)
  have heq : Finset.univ.sup' hne f =
      fun batch => Finset.univ.sup' hne (fun i => |value' (batch i) 0|) := by
    funext batch
    rw [Finset.sup'_apply hne f batch]
  change Measurable (fun batch : GenerationBatch N =>
    Finset.univ.sup' hne (fun i => |value' (batch i) 0|))
  rw [← heq]
  exact hsup

/-- An integrable leftmost-child displacement gives an integrable envelope
for a finite generation batch. -/
theorem integrable_infiniteOffspringBatchSlotZeroNorm {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ) :
    Integrable (infiniteOffspringBatchSlotZeroNorm hN)
      (generationBatchLaw μ N) := by
  let g : Step ℕ ℝ → ℝ := fun ξ => |value' ξ 0|
  have hsum : Integrable (fun batch : GenerationBatch N => ∑ i : Fin N, g (batch i))
      (generationBatchLaw μ N) := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    have hmap : Integrable g
        ((generationBatchLaw μ N).map (fun batch => batch i)) := by
      rw [generationBatchLaw_parent_marginal μ i]
      exact hslot
    exact (integrable_map_measure hmap.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).mp hmap
  have henvMeas : Measurable (infiniteOffspringBatchSlotZeroNorm hN) :=
    measurable_infiniteOffspringBatchSlotZeroNorm hN
  apply hsum.mono' henvMeas.aestronglyMeasurable
  filter_upwards [] with batch
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · calc
      infiniteOffspringBatchSlotZeroNorm hN batch ≤ ∑ i : Fin N, g (batch i) := by
        apply Finset.sup'_le
        intro i hi
        exact Finset.single_le_sum
          (f := fun j : Fin N => |value' (batch j) 0|)
          (fun j hj => abs_nonneg _) (Finset.mem_univ i)
      _ = ∑ i : Fin N, |value' (batch i) 0| := rfl
  · exact le_trans (abs_nonneg _) <|
      Finset.le_sup' (fun i : Fin N => |value' (batch i) 0|) (Finset.mem_univ ⟨0, hN⟩)

/-- Repairing invalid rows does not change the one-generation envelope
almost surely under the branching assumptions, so the repaired envelope
inherits the one-step moment bound. -/
theorem integrable_repairedInfiniteOffspringBatchSlotZeroNorm {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ) :
    Integrable
      (fun batch : GenerationBatch N =>
        infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch batch))
      (generationBatchLaw μ N) := by
  have hraw := integrable_infiniteOffspringBatchSlotZeroNorm hN μ hslot
  have hgood := generationBatchLaw_ae_isGoodInfiniteOffspringBatch
    μ hboundary hnonempty N
  have heq : (fun batch : GenerationBatch N =>
      infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch batch)) =ᵐ[
        generationBatchLaw μ N]
      fun batch => infiniteOffspringBatchSlotZeroNorm hN batch := by
    filter_upwards [hgood] with batch hb
    rw [repairGenerationBatch_eq_of_repairable batch hb]
  exact hraw.congr heq.symm

/-- The batch repair is measurable; the valid-domain predicate is measurable
by the coordinate sigma-algebra and the pointwise offspring observables. -/
theorem measurable_repairGenerationBatch {N : ℕ} :
    Measurable (repairGenerationBatch (N := N)) := by
  classical
  unfold repairGenerationBatch
  exact Measurable.ite isRepairableBatch_measurable measurable_id measurable_const

/-- Repair each generation independently as a deterministic map of its row. -/
noncomputable def repairGenerationEnvironment {N : ℕ} (ω : GenerationEnvironment N) :
    GenerationEnvironment N := fun n => repairGenerationBatch (ω n)

theorem measurable_repairGenerationEnvironment {N : ℕ} :
    Measurable (repairGenerationEnvironment (N := N)) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_repairGenerationBatch.comp (measurable_pi_apply n)

theorem repairGenerationEnvironment_commutes_shift {N : ℕ}
    (ω : GenerationEnvironment N) :
    repairGenerationEnvironment (generationEnvironmentShift ω) =
      generationEnvironmentShift (repairGenerationEnvironment ω) := by
  rfl

theorem repairGenerationEnvironment_ae_eq_self
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) (N : ℕ) :
    repairGenerationEnvironment (N := N) =ᵐ[generationEnvironmentLaw μ N] id := by
  filter_upwards [generationEnvironmentLaw_ae_allGood μ hboundary hnonempty N] with ω hω
  funext n
  apply repairGenerationBatch_eq_of_repairable
  exact hω n

/-- The generation sequence obtained by repairing every batch in an
environment. -/
noncomputable def repairedGenerationBatchSeq {N : ℕ}
    (ω : GenerationEnvironment N) : ℕ → GenerationBatch N :=
  fun t => repairGenerationBatch (ω t)

theorem repairedGenerationBatchSeq_good {N : ℕ}
    (ω : GenerationEnvironment N) :
    ∀ t, IsGoodInfiniteOffspringBatch (repairedGenerationBatchSeq ω t) := by
  intro t
  change IsRepairableBatch (repairGenerationBatch (ω t))
  exact repairGenerationBatch_repairable (ω t)

/-- Iterate the measurable totalized transition along the repaired
generation environment. -/
noncomputable def measurableRepairedInfiniteOffspringRun {N : ℕ} :
    ℕ → ((Fin N → ℝ) × GenerationEnvironment N) → (Fin N → ℝ)
  | 0 => fun x => x.1
  | n + 1 => fun x => totalizedInfiniteOffspringTransition
      (measurableRepairedInfiniteOffspringRun n x,
        repairGenerationBatch (x.2 n))

theorem measurable_measurableRepairedInfiniteOffspringRun {N : ℕ}
    (n : ℕ) : Measurable (measurableRepairedInfiniteOffspringRun (N := N) n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      simp only [measurableRepairedInfiniteOffspringRun]
      apply measurable_totalizedInfiniteOffspringTransition.comp
      exact Measurable.prodMk ih
        (measurable_repairGenerationBatch.comp
          ((measurable_pi_apply n).comp measurable_snd))

/-- The measurable recursion agrees everywhere with the original transition
recursion driven by the repaired batches. -/
theorem measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun
    {N : ℕ} (n : ℕ) (x : (Fin N → ℝ) × GenerationEnvironment N) :
    measurableRepairedInfiniteOffspringRun n x =
      infiniteOffspringRun
        (fun t => repairGenerationBatch (x.2 t))
        (fun t => repairGenerationBatch_repairable (x.2 t)) x.1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hgood : ∀ t,
          IsGoodInfiniteOffspringBatch (repairGenerationBatch (x.2 t)) := by
        intro t
        change IsRepairableBatch (repairGenerationBatch (x.2 t))
        exact repairGenerationBatch_repairable (x.2 t)
      change totalizedInfiniteOffspringTransition
          (measurableRepairedInfiniteOffspringRun n x,
            repairGenerationBatch (x.2 n)) =
        infiniteOffspringTransition
          (infiniteOffspringRun (fun t => repairGenerationBatch (x.2 t))
            hgood x.1 n)
          (repairGenerationBatch (x.2 n)) (hgood n)
      rw [ih]
      exact totalizedInfiniteOffspringTransition_eq_of_good
        (infiniteOffspringRun (fun t => repairGenerationBatch (x.2 t))
          hgood x.1 n)
        (repairGenerationBatch (x.2 n)) (hgood n)

/-- The negative leftmost endpoint of a repaired block, represented as a
measurable function of the original environment. -/
noncomputable def repairedInfiniteSelectionSubadditiveArray {N : ℕ}
    (hN : 0 < N) (ω : GenerationEnvironment N)
    (start length : ℕ) : ℝ :=
  - measurableRepairedInfiniteOffspringRun length
      ((fun _ : Fin N => (0 : ℝ)), fun t => ω (start + t)) ⟨0, hN⟩

theorem measurable_repairedInfiniteSelectionSubadditiveArray {N : ℕ}
    (hN : 0 < N) (start length : ℕ) :
    Measurable (fun ω : GenerationEnvironment N =>
      repairedInfiniteSelectionSubadditiveArray hN ω start length) := by
  have hshift : Measurable fun ω : GenerationEnvironment N =>
      fun t => ω (start + t) := by
    rw [measurable_pi_iff]
    intro t
    exact measurable_pi_apply (start + t)
  have hinput : Measurable fun ω : GenerationEnvironment N =>
      ((fun _ : Fin N => (0 : ℝ)), fun t => ω (start + t)) :=
    Measurable.prodMk measurable_const hshift
  have hrun : Measurable fun ω : GenerationEnvironment N =>
      measurableRepairedInfiniteOffspringRun length
        ((fun _ : Fin N => 0), fun t => ω (start + t)) :=
    (measurable_measurableRepairedInfiniteOffspringRun length).comp hinput
  exact (Measurable.eval (a := (⟨0, hN⟩ : Fin N)) hrun).neg

/-- The repaired one-generation envelope remains integrable after reading a
fixed row of the i.i.d. generation environment. -/
theorem integrable_repairedInfiniteOffspringBatchSlotZeroNorm_at {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ) (t : ℕ) :
    Integrable
      (fun ω : GenerationEnvironment N =>
        infiniteOffspringBatchSlotZeroNorm hN
          (repairGenerationBatch (ω t)))
      (generationEnvironmentLaw μ N) := by
  let f : GenerationBatch N → ℝ := fun batch =>
    infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch batch)
  have hbatch := integrable_repairedInfiniteOffspringBatchSlotZeroNorm
    hN μ hboundary hnonempty hslot
  have hmap : Integrable f
      ((generationEnvironmentLaw μ N).map (fun ω : GenerationEnvironment N => ω t)) := by
    rw [generationEnvironmentLaw_generation_marginal μ N t]
    exact hbatch
  exact (integrable_map_measure hmap.aestronglyMeasurable
    (measurable_pi_apply t).aemeasurable).mp hmap

/-- The measurable block array is the deterministic subadditive array of
the repaired generation sequence. -/
theorem repairedInfiniteSelectionSubadditiveArray_eq_deterministic
    {N : ℕ} (hN : 0 < N) (ω : GenerationEnvironment N)
    (start length : ℕ) :
    repairedInfiniteSelectionSubadditiveArray hN ω start length =
      infiniteSelectionSubadditiveArray hN (repairedGenerationBatchSeq ω)
        (repairedGenerationBatchSeq_good ω) start length := by
  unfold repairedInfiniteSelectionSubadditiveArray
    infiniteSelectionSubadditiveArray infiniteSelectionBlockMinimum
  have hrun := measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun
    length ((fun _ : Fin N => 0), fun t => ω (start + t))
  exact congrArg (fun state : Fin N → ℝ => -state ⟨0, hN⟩) hrun

/-- Almost surely, the absolute block endpoint is bounded by the sum of the
repaired generation-wise leftmost-child envelopes. -/
theorem repairedInfiniteSelectionSubadditiveArray_ae_abs_le_envelope
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hordered : μ (orderedBySteps realPotential) = 1)
    (hnonempty : μ nonemptySupport = 1) (n : ℕ) :
    ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      |repairedInfiniteSelectionSubadditiveArray hN ω 0 n| ≤
        ∑ t ∈ Finset.range n,
          infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch (ω t)) := by
  filter_upwards [generationEnvironmentLaw_ae_allOrderedFirst μ hordered hnonempty N]
    with ω hω
  have horderedRepair : ∀ t i,
      ((repairGenerationBatch (ω t)) i).IsOrderedBy realPotential := by
    intro t i
    exact (repairGenerationBatch_orderedFirst_of_orderedFirst (ω t)
      (hω t) i).1
  have hfirstRepair : ∀ t i,
      survive ((repairGenerationBatch (ω t)) i) 0 := by
    intro t i
    exact (repairGenerationBatch_orderedFirst_of_orderedFirst (ω t)
      (hω t) i).2
  have hpoint :
      |repairedInfiniteSelectionSubadditiveArray hN ω 0 n| ≤
        ∑ t ∈ Finset.range n,
          infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch (ω t)) := by
    rw [repairedInfiniteSelectionSubadditiveArray_eq_deterministic]
    simpa [repairedGenerationBatchSeq] using infiniteSelectionSubadditiveArray_abs_le hN
      (repairedGenerationBatchSeq ω) (repairedGenerationBatchSeq_good ω)
      horderedRepair hfirstRepair n
  exact hpoint

/-- The block endpoint array is integrable under the paper's one-step
leftmost-child moment condition and the ordered, nonempty offspring support.
The proof uses the deterministic sup-norm recursion, then integrates its
finite sum of generation envelopes. -/
theorem repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hordered : μ (orderedBySteps realPotential) = 1)
    (hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ)
    (n : ℕ) :
    Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N) := by
  let D : GenerationEnvironment N → ℕ → ℝ := fun ω t =>
    infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch (ω t))
  have hD : ∀ t, Integrable (fun ω => D ω t) (generationEnvironmentLaw μ N) := by
    intro t
    exact integrable_repairedInfiniteOffspringBatchSlotZeroNorm_at
      hN μ hboundary hnonempty hslot t
  have hsum : Integrable (fun ω => ∑ t ∈ Finset.range n, D ω t)
      (generationEnvironmentLaw μ N) := by
    apply integrable_finsetSum (Finset.range n)
    intro t ht
    exact hD t
  have hmeas := measurable_repairedInfiniteSelectionSubadditiveArray hN 0 n
  apply hsum.mono' hmeas.aestronglyMeasurable
  filter_upwards [repairedInfiniteSelectionSubadditiveArray_ae_abs_le_envelope
    hN μ hordered hnonempty n] with ω hω
  rw [Real.norm_eq_abs]
  simpa [D] using hω

/-- The one-step leftmost-child moment also supplies Kingman's normalized
expected-value lower bound. Stationarity makes each generation envelope have
the same finite mean, so the expected block lower bound is linear in its
length. -/
theorem repairedInfiniteSelection_normalizedIntegral_bddBelow_of_leftmostMoment
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hordered : μ (orderedBySteps realPotential) = 1)
    (hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ) :
    BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1)) := by
  let ν := generationEnvironmentLaw μ N
  let batchNorm : GenerationBatch N → ℝ := fun batch =>
    infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch batch)
  let D : GenerationEnvironment N → ℕ → ℝ := fun ω t => batchNorm (ω t)
  let c : ℝ := ∫ batch, batchNorm batch ∂generationBatchLaw μ N
  have hbatchNorm : Integrable batchNorm (generationBatchLaw μ N) := by
    exact integrable_repairedInfiniteOffspringBatchSlotZeroNorm
      hN μ hboundary hnonempty hslot
  have hD : ∀ t, Integrable (fun ω => D ω t) ν := by
    intro t
    exact integrable_repairedInfiniteOffspringBatchSlotZeroNorm_at
      hN μ hboundary hnonempty hslot t
  have hrowIntegral (t : ℕ) : (∫ ω, D ω t ∂ν) = c := by
    have hmapInt : Integrable batchNorm (ν.map (fun ω : GenerationEnvironment N => ω t)) := by
      rw [generationEnvironmentLaw_generation_marginal μ N t]
      exact hbatchNorm
    calc
      (∫ ω, D ω t ∂ν) =
          ∫ batch, batchNorm batch ∂ν.map (fun ω : GenerationEnvironment N => ω t) := by
            dsimp [D]
            exact (integral_map (measurable_pi_apply t).aemeasurable
              hmapInt.aestronglyMeasurable).symm
      _ = c := by
        rw [generationEnvironmentLaw_generation_marginal μ N t]
  have harrayInt (n : ℕ) : Integrable
      (fun ω => repairedInfiniteSelectionSubadditiveArray hN ω 0 n) ν := by
    exact repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment
      hN μ hboundary hnonempty hordered hslot n
  have hsumInt (n : ℕ) : Integrable
      (fun ω => ∑ t ∈ Finset.range n, D ω t) ν := by
    apply integrable_finsetSum (Finset.range n)
    intro t ht
    exact hD t
  have hsumIntegral (n : ℕ) :
      (∫ ω, ∑ t ∈ Finset.range n, D ω t ∂ν) = (n : ℝ) * c := by
    rw [integral_finsetSum (Finset.range n) (fun t ht => hD t)]
    calc
      (∑ t ∈ Finset.range n, ∫ ω, D ω t ∂ν) =
          ∑ t ∈ Finset.range n, c := by
            apply Finset.sum_congr rfl
            intro t ht
            exact hrowIntegral t
      _ = (n : ℝ) * c := by simp [Finset.sum_const, Finset.card_range]
  have hlower (n : ℕ) :
      -((n : ℝ) * c) ≤
        ∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 n ∂ν := by
    have hpath := repairedInfiniteSelectionSubadditiveArray_ae_abs_le_envelope
      hN μ hordered hnonempty n
    have haeLower : ∀ᵐ ω ∂ν,
        -(∑ t ∈ Finset.range n, D ω t) ≤
          repairedInfiniteSelectionSubadditiveArray hN ω 0 n := by
      filter_upwards [hpath] with ω hω
      exact neg_le_of_abs_le (by simpa [D] using hω)
    have hmono := integral_mono_ae (hsumInt n).neg (harrayInt n) haeLower
    have hmono' :
        (∫ ω, -(∑ t ∈ Finset.range n, D ω t) ∂ν) ≤
          ∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 n ∂ν := by
      simpa using hmono
    rw [integral_neg, hsumIntegral n] at hmono'
    simpa using hmono'
  have hnormalized (n : ℕ) : -c ≤
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1) ∂ν) / (n + 1) := by
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hnpos]
    have hlower' := hlower (n + 1)
    have hlower'' : -(((n : ℝ) + 1) * c) ≤
        ∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1) ∂ν := by
      simpa [Nat.cast_add, Nat.cast_one] using hlower'
    have hmul : -c * ((n : ℝ) + 1) = -(((n : ℝ) + 1) * c) := by ring
    rw [hmul]
    exact hlower''
  refine ⟨-c, ?_⟩
  rintro x ⟨n, rfl⟩
  exact hnormalized n

theorem repairedInfiniteSelectionSubadditiveArray_subadditive
    {N : ℕ} (hN : 0 < N) (ω : GenerationEnvironment N)
    (start firstLength secondLength : ℕ) :
    repairedInfiniteSelectionSubadditiveArray hN ω start
        (firstLength + secondLength) ≤
      repairedInfiniteSelectionSubadditiveArray hN ω start firstLength +
        repairedInfiniteSelectionSubadditiveArray hN ω (start + firstLength)
          secondLength := by
  rw [repairedInfiniteSelectionSubadditiveArray_eq_deterministic,
    repairedInfiniteSelectionSubadditiveArray_eq_deterministic,
    repairedInfiniteSelectionSubadditiveArray_eq_deterministic]
  exact infiniteSelectionSubadditiveArray_subadditive hN
    (repairedGenerationBatchSeq ω) (repairedGenerationBatchSeq_good ω)
    start firstLength secondLength

/-- Starting a repaired environment at a later generation agrees with
advancing the block's start time. -/
theorem repairedInfiniteSelectionSubadditiveArray_suffix
    {N : ℕ} (hN : 0 < N) (ω : GenerationEnvironment N)
    (shift start length : ℕ) :
    repairedInfiniteSelectionSubadditiveArray hN
        (fun t => ω (shift + t)) start length =
      repairedInfiniteSelectionSubadditiveArray hN ω (shift + start) length := by
  rw [repairedInfiniteSelectionSubadditiveArray_eq_deterministic,
    repairedInfiniteSelectionSubadditiveArray_eq_deterministic]
  change infiniteSelectionSubadditiveArray hN
      (fun t => repairGenerationBatch (ω (shift + t)))
      (fun t => repairedGenerationBatchSeq_good (fun t => ω (shift + t)) t)
      start length =
    infiniteSelectionSubadditiveArray hN
      (fun t => repairGenerationBatch (ω t))
      (fun t => repairedGenerationBatchSeq_good ω t)
      (shift + start) length
  exact infiniteSelectionSubadditiveArray_shift_covariant hN
    (fun t => repairGenerationBatch (ω t))
    (fun t => repairedGenerationBatchSeq_good ω t)
    shift start length

/-- Iterating the one-sided environment shift by `m` is the same as dropping
the first `m` generations. -/
theorem generationEnvironmentShift_iterate {N : ℕ}
    (m : ℕ) (ω : GenerationEnvironment N) :
    (generationEnvironmentShift^[m]) ω = fun t => ω (m + t) := by
  induction m generalizing ω with
  | zero =>
      funext t
      simp
  | succ m ih =>
      funext t
      rw [Function.iterate_succ_apply]
      rw [ih (generationEnvironmentShift ω)]
      simp only [generationEnvironmentShift]
      congr 1
      omega

/-- The measurable repaired block array is a subadditive cocycle over the
generation shift, so it can be passed directly to the repository's Kingman
theorem. -/
theorem repairedInfiniteSelection_isSubadditiveCocycle {N : ℕ}
    (hN : 0 < N) :
    IsSubadditiveCocycle (generationEnvironmentShift :
      GenerationEnvironment N → GenerationEnvironment N)
      (fun n ω => repairedInfiniteSelectionSubadditiveArray hN ω 0 n) := by
  refine ⟨?_⟩
  intro m n ω
  calc
    repairedInfiniteSelectionSubadditiveArray hN ω 0 (m + n) ≤
        repairedInfiniteSelectionSubadditiveArray hN ω 0 m +
          repairedInfiniteSelectionSubadditiveArray hN ω m n := by
      simpa using repairedInfiniteSelectionSubadditiveArray_subadditive
        hN ω 0 m n
    _ = repairedInfiniteSelectionSubadditiveArray hN ω 0 m +
        repairedInfiniteSelectionSubadditiveArray hN
          ((generationEnvironmentShift^[m]) ω) 0 n := by
      congr 1
      rw [generationEnvironmentShift_iterate]
      simpa [Nat.zero_add, Nat.add_zero] using
        (repairedInfiniteSelectionSubadditiveArray_suffix hN ω m 0 n).symm

/-- Apply the full Kingman theorem to the repaired finite-selection array.
Besides almost-sure convergence, it returns an integrable limit invariant
under the generation shift. The two analytic inputs are stated explicitly:
integrability of every block length and a uniform lower bound on normalized
expected block values. -/
theorem repairedInfiniteSelection_tendsto_invariant_integrable {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N))
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1))) :
    ∃ G : GenerationEnvironment N → ℝ,
      (G ∘ generationEnvironmentShift =ᵐ[generationEnvironmentLaw μ N] G) ∧
      Integrable G (generationEnvironmentLaw μ N) ∧
      ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
        atTop (𝓝 (G ω)) := by
  let ν := generationEnvironmentLaw μ N
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  letI := hν
  exact ProbabilityTheory.tendsto_kingman
    (generationEnvironmentLaw_shift_measurePreserving μ N)
    (repairedInfiniteSelection_isSubadditiveCocycle hN) hint hbdd

/-- In the i.i.d. generation environment the invariant Kingman limit is
almost surely constant, giving the scalar-speed form of the theorem. -/
theorem repairedInfiniteSelection_tendsto_constant {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N))
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
        atTop (𝓝 c) := by
  let ν := generationEnvironmentLaw μ N
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  letI := hν
  obtain ⟨G, hGinv, hGint, hGconv⟩ :=
    repairedInfiniteSelection_tendsto_invariant_integrable hN μ hint hbdd
  have hErg := generationEnvironmentShift_ergodic μ N
  obtain ⟨c, hc⟩ := hErg.ae_eq_const_of_ae_eq_comp_ae
    hGint.aestronglyMeasurable hGinv
  refine ⟨c, ?_⟩
  filter_upwards [hGconv, hc] with ω hω hωc
  simpa [hωc] using hω

/-- The first-row Kingman limit also holds in `L¹` under the same one-step
leftmost-child moment condition used to prove integrability and the lower
bound. The proof dominates the normalized endpoint array by averages of the
i.i.d. generation envelope, obtains uniform integrability from Mathlib's
uniform-integrability API, and applies Vitali convergence to the almost-sure
Kingman limit.

This is still the speed result for exactly `N` particles. It does not include
the paper's extension from an initial population of size `N₀ ≤ N` to size
`N`; that extension needs a finite-time saturation/restart argument for the
root-indexed selected-population process. -/
theorem repairedInfiniteSelection_tendsto_constant_L1_of_leftmostMoment
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hordered : μ (orderedBySteps realPotential) = 1)
    (hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ) :
    ∃ c : ℝ,
      (∀ᵐ ω ∂generationEnvironmentLaw μ N,
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
          atTop (𝓝 c)) ∧
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω : GenerationEnvironment N =>
            (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c)
          (1 : ℝ≥0∞) (generationEnvironmentLaw μ N))
        atTop (𝓝 0) := by
  let ν := generationEnvironmentLaw μ N
  let D : ℕ → GenerationEnvironment N → ℝ := fun t ω =>
    infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch (ω t))
  let f : ℕ → GenerationEnvironment N → ℝ := fun n ω =>
    (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n
  let g : ℕ → GenerationEnvironment N → ℝ := fun n ω =>
    (∑ t ∈ Finset.range n, D t ω) / (n : ℝ)
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  letI := hν
  have hDint (t : ℕ) : Integrable (D t) ν := by
    exact integrable_repairedInfiniteOffspringBatchSlotZeroNorm_at
      hN μ hboundary hnonempty hslot t
  have hD0 : MemLp (D 0) (1 : ℝ≥0∞) ν :=
    MeasureTheory.memLp_one_iff_integrable.mpr (hDint 0)
  have hbatchMeas : Measurable
      (fun batch : GenerationBatch N =>
        infiniteOffspringBatchSlotZeroNorm hN (repairGenerationBatch batch)) :=
    (measurable_infiniteOffspringBatchSlotZeroNorm hN).comp
      measurable_repairGenerationBatch
  have hcoord (t : ℕ) : IdentDistrib (fun ω : GenerationEnvironment N => ω t)
      (fun ω : GenerationEnvironment N => ω 0) ν ν := by
    refine ⟨(measurable_pi_apply t).aemeasurable,
      (measurable_pi_apply 0).aemeasurable, ?_⟩
    rw [generationEnvironmentLaw_generation_marginal μ N t,
      generationEnvironmentLaw_generation_marginal μ N 0]
  have hDident (t : ℕ) : IdentDistrib (D t) (D 0) ν ν := by
    simpa [D, Function.comp_def] using (hcoord t).comp hbatchMeas
  have hDui : UniformIntegrable D (1 : ℝ≥0∞) ν :=
    MemLp.uniformIntegrable_of_identDistrib (by norm_num) (by norm_num)
      hD0 hDident
  have havg : UniformIntegrable g (1 : ℝ≥0∞) ν := by
    have h := uniformIntegrable_average_real (p := (1 : ℝ≥0∞))
      (by norm_num) hDui
    convert h using 1
    ext n ω
    simp [g, D, div_eq_mul_inv, mul_comm]
  have hDnonneg (t : ℕ) (ω : GenerationEnvironment N) : 0 ≤ D t ω := by
    dsimp [D]
    unfold infiniteOffspringBatchSlotZeroNorm
    exact le_trans (abs_nonneg _) <| Finset.le_sup'
      (fun i : Fin N => |value' (repairGenerationBatch (ω t) i) 0|)
      (Finset.mem_univ ⟨0, hN⟩)
  have hg_nonneg (n : ℕ) (ω : GenerationEnvironment N) : 0 ≤ g n ω := by
    dsimp [g]
    exact div_nonneg (Finset.sum_nonneg fun t ht => hDnonneg t ω)
      (Nat.cast_nonneg n)
  have hdom (n : ℕ) : ∀ᵐ ω ∂ν, |f n ω| ≤ g n ω := by
    by_cases hn : n = 0
    · subst n
      filter_upwards [] with ω
      simp [f, g, repairedInfiniteSelectionSubadditiveArray]
    · filter_upwards [repairedInfiniteSelectionSubadditiveArray_ae_abs_le_envelope
        hN μ hordered hnonempty n] with ω hω
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hinv : 0 ≤ (n : ℝ)⁻¹ := (inv_nonneg.mpr hnpos.le)
      calc
        |f n ω| = (n : ℝ)⁻¹ *
            |repairedInfiniteSelectionSubadditiveArray hN ω 0 n| := by
              simp [f, abs_mul, abs_of_nonneg hinv]
        _ ≤ (n : ℝ)⁻¹ * (∑ t ∈ Finset.range n, D t ω) := by
              exact mul_le_mul_of_nonneg_left (by simpa [D] using hω) hinv
        _ = g n ω := by
              simp [g, div_eq_mul_inv, mul_comm]
  have hfmeas (n : ℕ) : AEStronglyMeasurable (f n) ν := by
    dsimp [f]
    exact (measurable_const.mul
      (measurable_repairedInfiniteSelectionSubadditiveArray hN 0 n)).aestronglyMeasurable
  have hui : UnifIntegrable f (1 : ℝ≥0∞) ν := by
    apply havg.unifIntegrable.ae_mono hfmeas
    intro n
    filter_upwards [hdom n] with ω hω
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hg_nonneg n ω)]
    exact ENNReal.ofReal_le_ofReal hω
  have hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n) ν := by
    intro n
    exact repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment
      hN μ hboundary hnonempty hordered hslot n
  have hbdd := repairedInfiniteSelection_normalizedIntegral_bddBelow_of_leftmostMoment
    hN μ hboundary hnonempty hordered hslot
  obtain ⟨c, hconv⟩ := repairedInfiniteSelection_tendsto_constant hN μ hint hbdd
  have hL1 : Tendsto
      (fun n : ℕ => eLpNorm (fun ω : GenerationEnvironment N => f n ω - c)
        (1 : ℝ≥0∞) ν) atTop (𝓝 0) := by
    apply MeasureTheory.tendsto_Lp_finite_of_tendsto_ae
      (μ := ν) (p := (1 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (fun n => hfmeas n) (memLp_const c) hui
    simpa only [f] using hconv
  refine ⟨c, ?_, ?_⟩
  · simpa only [f] using hconv
  · simpa only [f] using hL1

/-- On an environment whose every generation is a valid transition, repairing
the environment leaves the deterministic selection array unchanged. -/
theorem repairedInfiniteSelectionSubadditiveArray_eq_of_allGood {N : ℕ}
    (hN : 0 < N) (ω : GenerationEnvironment N)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t))
    (start length : ℕ) :
    repairedInfiniteSelectionSubadditiveArray hN ω start length =
      infiniteSelectionSubadditiveArray hN ω hgood start length := by
  rw [repairedInfiniteSelectionSubadditiveArray_eq_deterministic]
  have hseq : repairedGenerationBatchSeq ω = ω := by
    funext t
    exact repairGenerationBatch_eq_of_repairable (ω t) (hgood t)
  unfold infiniteSelectionSubadditiveArray infiniteSelectionBlockMinimum
  apply congrArg (fun state : Fin N → ℝ => -state ⟨0, hN⟩)
  exact infiniteOffspringRun_congr
    (fun t => repairedGenerationBatchSeq ω (start + t))
    (fun t => ω (start + t))
    (by
      funext t
      exact congrFun hseq (start + t))
    (fun t => repairedGenerationBatchSeq_good ω (start + t))
    (fun t => hgood (start + t))
    (fun _ => 0)
    length

/-- Under the model's boundary-normalization and nonempty-offspring
assumptions, the repaired Kingman limit is also the limit of the original
selection array almost surely. -/
theorem infiniteSelection_tendsto_constant {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N))
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            infiniteSelectionSubadditiveArray hN ω hgood 0 n)
          atTop (𝓝 c) := by
  obtain ⟨c, hconv⟩ := repairedInfiniteSelection_tendsto_constant
    hN μ hint hbdd
  refine ⟨c, ?_⟩
  filter_upwards [generationEnvironmentLaw_ae_allGood μ hboundary hnonempty N,
    hconv] with ω hgood hω
  refine ⟨hgood, ?_⟩
  apply hω.congr'
  filter_upwards [] with n
  rw [← repairedInfiniteSelectionSubadditiveArray_eq_of_allGood
    hN ω hgood 0 n]

/-- The first-row Kingman limit is the almost-sure asymptotic speed of the
leftmost particle in the original `N`-selection process started from the
origin. The witness `hgood` records the almost-sure validity of every sampled
generation needed by the deterministic recursion. -/
theorem infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed {N : ℕ}
    (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N))
    (hbdd : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw μ N) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
        Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
          (𝕜 := ℝ)
          (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
          (-c) := by
  obtain ⟨c, hconv⟩ := infiniteSelection_tendsto_constant
    hN μ hboundary hnonempty hint hbdd
  refine ⟨c, ?_⟩
  filter_upwards [hconv] with ω hω
  rcases hω with ⟨hgood, hlim⟩
  refine ⟨hgood, ?_⟩
  change Tendsto
    (fun n : ℕ => (n : ℝ)⁻¹ *
      infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
    atTop (𝓝 (-c))
  refine hlim.neg.congr' ?_
  filter_upwards [] with n
  simp [infiniteSelectionSubadditiveArray, infiniteSelectionBlockMinimum]

/-- The ordered, potential-projected realization has an almost-sure
leftmost speed under the paper's separate boundary, nonempty-offspring, and
leftmost first-moment assumptions. The integrability and normalized lower
bound required by Kingman are derived internally from those assumptions. -/
theorem infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_of_stepLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (L : StepLaw ι ℕ X)
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L) :
    ∃ c : ℝ,
      ∀ᵐ ω ∂generationEnvironmentLaw L.sortedPotentialImage N,
        ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
          Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
            (𝕜 := ℝ)
            (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
            (-c) := by
  let μ := L.sortedPotentialImage
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hboundaryμ : HasBoundaryNormalization realPotential μ :=
    L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  have horderedμ : μ (orderedBySteps realPotential) = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_orderedBy]
    simp
  have hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ :=
    L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
  have hint : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw μ N) := by
    intro n
    exact repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment
      hN μ hboundaryμ hnonemptyμ horderedμ hslot n
  have hbdd := repairedInfiniteSelection_normalizedIntegral_bddBelow_of_leftmostMoment
    hN μ hboundaryμ hnonemptyμ horderedμ hslot
  exact infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed
    hN μ hboundaryμ hnonemptyμ hint hbdd

/-! The speed and `L¹` conclusions for exactly `N` particles, in the paper's
`StepLaw` assumptions, are packaged together here. The rightmost result is
obtained by applying this theorem to the OrderDual/reflected law, with its own
right-side moment assumptions; no reflection invariance is required. -/
theorem infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {N : ℕ} (hN : 0 < N) (L : StepLaw ι ℕ X)
    [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L) :
    ∃ c : ℝ,
      (∀ᵐ ω ∂generationEnvironmentLaw L.sortedPotentialImage N,
        ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
          Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
            (𝕜 := ℝ)
            (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
            (-c)) ∧
      Tendsto
        (fun n : ℕ => eLpNorm
          (fun ω : GenerationEnvironment N =>
            (n : ℝ)⁻¹ * measurableRepairedInfiniteOffspringRun n
              ((fun _ : Fin N => (0 : ℝ)), ω) ⟨0, hN⟩ - (-c))
          (1 : ℝ≥0∞) (generationEnvironmentLaw L.sortedPotentialImage N))
        atTop (𝓝 0) := by
  let μ := L.sortedPotentialImage
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hboundaryμ : HasBoundaryNormalization realPotential μ :=
    L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
    exact hnonempty
  have horderedμ : μ (orderedBySteps realPotential) = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl,
      L.sortedPotentialImage_orderedBy]
    simp
  have hslot : Integrable (fun ξ : Step ℕ ℝ => |value' ξ 0|) μ :=
    L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
  let ν := generationEnvironmentLaw μ N
  haveI : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  obtain ⟨c, hconv, hL1⟩ :=
    repairedInfiniteSelection_tendsto_constant_L1_of_leftmostMoment
      hN μ hboundaryμ hnonemptyμ horderedμ hslot
  have hgood : ∀ᵐ ω ∂ν, ∀ t, IsGoodInfiniteOffspringBatch (ω t) :=
    generationEnvironmentLaw_ae_allGood μ hboundaryμ hnonemptyμ N
  have hconvOriginal : ∀ᵐ ω ∂ν,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            infiniteSelectionSubadditiveArray hN ω hgood 0 n)
          atTop (𝓝 c) := by
    filter_upwards [hgood, hconv] with ω hgoodω hω
    refine ⟨hgoodω, ?_⟩
    apply hω.congr'
    filter_upwards [] with n
    rw [← repairedInfiniteSelectionSubadditiveArray_eq_of_allGood
      hN ω hgoodω 0 n]
  have hspeed : ∀ᵐ ω ∂ν,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (ω t),
        Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
          (𝕜 := ℝ)
          (fun n => infiniteOffspringRun ω hgood (fun _ => 0) n ⟨0, hN⟩)
          (-c) := by
    filter_upwards [hconvOriginal] with ω hω
    rcases hω with ⟨hgoodω, hlim⟩
    refine ⟨hgoodω, ?_⟩
    change Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        infiniteOffspringRun ω hgoodω (fun _ => 0) n ⟨0, hN⟩)
      atTop (𝓝 (-c))
    have hneg := hlim.neg
    apply hneg.congr'
    filter_upwards [] with n
    simp [infiniteSelectionSubadditiveArray, infiniteSelectionBlockMinimum]
  let P : ℕ → GenerationEnvironment N → ℝ := fun n ω =>
    measurableRepairedInfiniteOffspringRun n
      ((fun _ : Fin N => (0 : ℝ)), ω) ⟨0, hN⟩
  have hL1position : Tendsto
      (fun n : ℕ => eLpNorm
        (fun ω : GenerationEnvironment N => (n : ℝ)⁻¹ * P n ω - (-c))
        (1 : ℝ≥0∞) ν) atTop (𝓝 0) := by
    have hnorm (n : ℕ) : eLpNorm
        (fun ω : GenerationEnvironment N => (n : ℝ)⁻¹ * P n ω - (-c))
        (1 : ℝ≥0∞) ν =
      eLpNorm
        (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c)
        (1 : ℝ≥0∞) ν := by
      have hfun : (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ * P n ω - (-c)) =
        fun ω => -((n : ℝ)⁻¹ *
          repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c) := by
        funext ω
        have harray : repairedInfiniteSelectionSubadditiveArray hN ω 0 n = -P n ω := by
          simp [P, repairedInfiniteSelectionSubadditiveArray]
        rw [harray]
        ring
      rw [hfun]
      exact eLpNorm_neg _ _ _
    have hseq : (fun n : ℕ => eLpNorm
        (fun ω : GenerationEnvironment N => (n : ℝ)⁻¹ * P n ω - (-c))
        (1 : ℝ≥0∞) ν) =
      fun (n : ℕ) => eLpNorm
        (fun ω : GenerationEnvironment N =>
          (n : ℝ)⁻¹ * repairedInfiniteSelectionSubadditiveArray hN ω 0 n - c)
        (1 : ℝ≥0∞) ν := by
      funext n
      exact hnorm n
    rw [hseq]
    simpa [ν, μ] using hL1
  exact ⟨c, by simpa [ν, μ] using hspeed, by simpa [ν, μ] using hL1position⟩

/-- Reflect every displacement while preserving exactly the same child slots.
This is the pathwise operation used to turn a rightmost selection into a
leftmost selection. -/
def reflectOffspringStep (ξ : Step ℕ ℝ) : Step ℕ ℝ :=
  Combinatorics.Branching.Step.map Neg.neg ξ

/-- Reflect all parent offspring steps in one generation. -/
def reflectGenerationBatch {N : ℕ} (batch : GenerationBatch N) :
    GenerationBatch N :=
  fun i => reflectOffspringStep (batch i)

/-- Reflect every generation and every displacement in a pre-sampled
environment. -/
def reflectGenerationEnvironment {N : ℕ} (ω : GenerationEnvironment N) :
    GenerationEnvironment N :=
  fun n => reflectGenerationBatch (ω n)

theorem measurable_reflectOffspringStep :
    Measurable reflectOffspringStep := by
  exact Combinatorics.Branching.Step.map_measurable measurable_neg

theorem measurable_reflectGenerationBatch {N : ℕ} :
    Measurable (reflectGenerationBatch (N := N)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_reflectOffspringStep.comp (measurable_pi_apply i)

theorem measurable_reflectGenerationEnvironment {N : ℕ} :
    Measurable (reflectGenerationEnvironment (N := N)) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_reflectGenerationBatch.comp (measurable_pi_apply n)

theorem generationBatchLaw_reflect_map {N : ℕ}
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    (generationBatchLaw μ N).map reflectGenerationBatch =
      generationBatchLaw (Measure.map reflectOffspringStep μ) N := by
  classical
  unfold generationBatchLaw
  change (Measure.pi (fun _ : Fin N => μ)).map
      (fun batch i => reflectOffspringStep (batch i)) =
        Measure.pi (fun _ : Fin N => Measure.map reflectOffspringStep μ)
  rw [Measure.pi_map_pi (hf := fun _ => measurable_reflectOffspringStep.aemeasurable)]

/-! Reflecting an i.i.d. environment changes its law to the environment law
of the reflected offspring distribution. No symmetry assumption on `μ` is
needed; the reflected law is the offspring law appropriate to `OrderDual`. -/
theorem generationEnvironmentLaw_reflect_map {N : ℕ}
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] :
    (generationEnvironmentLaw μ N).map reflectGenerationEnvironment =
      generationEnvironmentLaw (Measure.map reflectOffspringStep μ) N := by
  unfold generationEnvironmentLaw
  change (Measure.infinitePi (fun _ : ℕ => generationBatchLaw μ N)).map
      (fun ω n => reflectGenerationBatch (ω n)) =
        Measure.infinitePi
          (fun _ : ℕ =>
            generationBatchLaw (Measure.map reflectOffspringStep μ) N)
  rw [Measure.infinitePi_map_pi
    (fun _ : ℕ => generationBatchLaw μ N)
    (fun _ => measurable_reflectGenerationBatch)]
  simp_rw [generationBatchLaw_reflect_map μ]

/-- One rightmost transition is the reflection of a leftmost transition.
The rank index is therefore ordered from the greatest spatial position down.
The goodness witness is required for the reflected offspring batch, whose
lower tail controls existence of its first `N` children. -/
noncomputable def infiniteOffspringTransitionRight {N : ℕ}
    (position : Fin N → ℝ) (offspring : GenerationBatch N)
    (hgood : IsGoodInfiniteOffspringBatch (reflectGenerationBatch offspring)) :
    Fin N → ℝ :=
  fun i => - infiniteOffspringTransition (fun j => -position j)
    (reflectGenerationBatch offspring) hgood i

/-- Iterate rightmost-`N` selection by reflecting the same rank-indexed
offspring environment and negating the resulting positions. -/
noncomputable def infiniteOffspringRunRight {N : ℕ}
    (offspring : GenerationEnvironment N)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch
      (reflectGenerationBatch (offspring t)))
    (initial : Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => initial
  | n + 1 => infiniteOffspringTransitionRight
      (infiniteOffspringRunRight offspring hgood initial n)
      (offspring n) (hgood n)

theorem infiniteOffspringRunRight_eq_neg_reflected {N : ℕ}
    (offspring : GenerationEnvironment N)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch
      (reflectGenerationBatch (offspring t)))
    (initial : Fin N → ℝ) (n : ℕ) :
    infiniteOffspringRunRight offspring hgood initial n =
      fun i => - infiniteOffspringRun
        (fun t => reflectGenerationBatch (offspring t)) hgood
        (fun i => -initial i) n i := by
  induction n with
  | zero =>
      funext i
      simp [infiniteOffspringRunRight]
  | succ n ih =>
      funext i
      simp only [infiniteOffspringRunRight, infiniteOffspringTransitionRight,
        infiniteOffspringRun_succ]
      rw [ih]
      have hstate :
          (fun j : Fin N => - (fun i : Fin N =>
            -infiniteOffspringRun
              (fun t => reflectGenerationBatch (offspring t)) hgood
              (fun i => -initial i) n i) j) =
            infiniteOffspringRun
              (fun t => reflectGenerationBatch (offspring t)) hgood
              (fun i => -initial i) n := by
        funext j
        simp
      rw [hstate]

/-- The Kingman cocycle for the reflected environment is exactly the
rightmost position in the original coordinates. Thus its right-side endpoint
has a positive sign: `- leftmost(reflected) = rightmost(original)`. -/
theorem infiniteSelectionSubadditiveArray_reflect_eq_rightmost {N : ℕ}
    (hN : 0 < N) (offspring : GenerationEnvironment N)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch
      (reflectGenerationBatch (offspring t))) (n : ℕ) :
    infiniteSelectionSubadditiveArray hN
        (fun t => reflectGenerationBatch (offspring t)) hgood 0 n =
      infiniteOffspringRunRight offspring hgood (fun _ => 0) n ⟨0, hN⟩ := by
  unfold infiniteSelectionSubadditiveArray infiniteSelectionBlockMinimum
  simp only [Nat.zero_add]
  rw [infiniteOffspringRunRight_eq_neg_reflected offspring hgood
    (fun _ => 0) n]
  simp

/-! Applying the leftmost theorem to the OrderDual offspring law gives the
rightmost speed. The right-side boundary, integrability, and lower-bound
conditions are precisely the left-side hypotheses for the reflected law;
there is no reflection-invariance assumption on the original law. -/
theorem infiniteOffspringRun_rightmost_ae_hasAsymptoticSpeed
    {N : ℕ} (hN : 0 < N)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundaryDual : HasBoundaryNormalization realPotential
      (Measure.map reflectOffspringStep μ))
    (hnonemptyDual : (Measure.map reflectOffspringStep μ) nonemptySupport = 1)
    (hintDual : ∀ n, Integrable
      (fun ω : GenerationEnvironment N =>
        repairedInfiniteSelectionSubadditiveArray hN ω 0 n)
      (generationEnvironmentLaw (Measure.map reflectOffspringStep μ) N))
    (hbddDual : BddBelow (Set.range fun n : ℕ =>
      (∫ ω, repairedInfiniteSelectionSubadditiveArray hN ω 0 (n + 1)
        ∂generationEnvironmentLaw (Measure.map reflectOffspringStep μ) N) /
          (n + 1))) :
    ∃ cRight : ℝ, ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch
          (reflectGenerationBatch (ω t)),
        Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
          (𝕜 := ℝ)
          (fun n => infiniteOffspringRunRight ω hgood (fun _ => 0) n ⟨0, hN⟩)
          cRight := by
  let μDual : Measure (Step ℕ ℝ) := Measure.map reflectOffspringStep μ
  haveI : IsProbabilityMeasure μDual := by
    dsimp [μDual]
    infer_instance
  obtain ⟨c, hdual⟩ := infiniteOffspringRun_leftmost_ae_hasAsymptoticSpeed
    hN μDual hboundaryDual hnonemptyDual hintDual hbddDual
  let ν := generationEnvironmentLaw μ N
  haveI : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  have hmap : ν.map reflectGenerationEnvironment =
      generationEnvironmentLaw μDual N := by
    simpa [μDual] using generationEnvironmentLaw_reflect_map (N := N) μ
  have hdualPull : ∀ᵐ ω ∂ν,
      ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch
          (reflectGenerationBatch (ω t)),
        Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
          (𝕜 := ℝ)
          (fun n => infiniteOffspringRun
            (reflectGenerationEnvironment ω) hgood (fun _ => 0) n ⟨0, hN⟩)
          (-c) := by
    have hmapAE : ∀ᵐ η ∂ν.map reflectGenerationEnvironment,
        ∃ hgood : ∀ t, IsGoodInfiniteOffspringBatch (η t),
          Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
            (𝕜 := ℝ)
            (fun n => infiniteOffspringRun η hgood (fun _ => 0) n ⟨0, hN⟩)
            (-c) := by
      rw [hmap]
      exact hdual
    have hpull := ae_of_ae_map
      measurable_reflectGenerationEnvironment.aemeasurable hmapAE
    simpa only [reflectGenerationEnvironment] using hpull
  refine ⟨c, ?_⟩
  filter_upwards [hdualPull] with ω hω
  rcases hω with ⟨hgoodReflect, hreflectedSpeed⟩
  refine ⟨hgoodReflect, ?_⟩
  have hrightNeg :
      Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
        (𝕜 := ℝ)
      (fun n => -infiniteOffspringRun
        (reflectGenerationEnvironment ω) hgoodReflect
          (fun _ => 0) n ⟨0, hN⟩) c := by
    change Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      (-infiniteOffspringRun
        (reflectGenerationEnvironment ω) hgoodReflect
        (fun _ => 0) n ⟨0, hN⟩)) atTop (𝓝 c)
    have hneg := hreflectedSpeed.neg
    convert hneg using 1 <;> ext n <;> simp [mul_neg]
  have hpath :
      (fun n => infiniteOffspringRunRight ω hgoodReflect (fun _ => 0)
        n ⟨0, hN⟩) =
      (fun n => -infiniteOffspringRun
        (reflectGenerationEnvironment ω) hgoodReflect
        (fun _ => 0) n ⟨0, hN⟩) := by
    funext n
    rw [infiniteOffspringRunRight_eq_neg_reflected]
    simp only [neg_zero]
    have hrun := infiniteOffspringRun_congr
      (fun t => reflectGenerationBatch (ω t))
      (reflectGenerationEnvironment ω)
      (by funext t; rfl)
      hgoodReflect hgoodReflect (fun _ => 0) n
    rw [hrun]
  simpa only [hpath] using hrightNeg

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
