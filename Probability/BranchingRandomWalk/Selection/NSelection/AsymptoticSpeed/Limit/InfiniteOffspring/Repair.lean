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
public import Combinatorics.BranchingWalk.Selection.NSelection.Walk.Speed
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.IdentDistrib

/-!
# Measurable repair of infinite-offspring environments

This module repairs invalid generation batches to a canonical valid batch and
constructs the measurable recursion driven by the repaired environment.
It also installs the countability and discrete measurable-space instances
for `InfiniteSlotLabel N` used by that recursion.

- `fallbackOffspringStep` and `fallbackGenerationBatch`: the canonical
  one-child batch at displacement zero.
- `IsRepairableBatch`: the predicate that a batch satisfies
  `IsGoodInfiniteOffspringBatch`.
- `isRepairableBatch_measurable`: measurability of that validity predicate.
- `totalizedInfiniteOffspringFirstN`: the measurable totalized first-`N`
  offspring selector.
- `totalizedInfiniteOffspringRankOption` and
  `totalizedInfiniteOffspringRankLabel`: rank lookup before and after
  replacing a missing rank by the default label.
- `totalizedInfiniteOffspringTransition`: the resulting totalized
  one-generation transition.
- `repairGenerationBatch`: the identity on repairable batches and the
  canonical fallback on other batches.
- `measurable_repairGenerationBatch`: measurability of the batch repair map.
- `repairGenerationBatch_repairable`: every repaired batch is repairable.
- `repairGenerationBatch_eq_of_repairable`: a repairable batch is fixed by
  the repair map.
- `repairGenerationBatch_orderedFirst_of_orderedFirst`: the repair preserves
  ordered batches with a surviving slot-zero child.
- `generationEnvironmentLaw_ae_allOrderedFirst`: if a one-step law is
  supported on ordered, nonempty batches, then almost every i.i.d. environment
  has that property at every generation.
- `repairGenerationEnvironment`: the pointwise repair of every generation.
- `measurable_repairGenerationEnvironment`: measurability of that map.
- `repairGenerationEnvironment_commutes_shift`: repairing then shifting is
  equal to shifting then repairing.
- `repairGenerationEnvironment_ae_eq_self`: under the boundary and
  nonempty-support assumptions, the repaired environment equals the original
  almost surely.
- `measurableRepairedInfiniteOffspringRun`: the totalized measurable run
  driven by repaired batches.
- `measurable_measurableRepairedInfiniteOffspringRun`: measurability of each
  time-indexed run map.
- `measurableRepairedInfiniteOffspringRun_eq_infiniteOffspringRun`: the
  measurable run agrees pointwise with the ordinary selection recursion on
  the repaired environment.
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

private theorem fallbackOffspringStep_totalChildWeight :
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

private lemma infiniteOffspringCandidate_mem_measurable {N : ℕ}
    (q : InfiniteSlotLabel N) :
    Measurable fun batch : GenerationBatch N =>
      q ∈ infiniteOffspringCandidates batch := by
  apply measurableSet_setOfPred.mp
  change MeasurableSet
    {batch : GenerationBatch N |
      survive (batch (ofLex q).1) (ofLex q).2}
  exact (survive_measurableSet (ofLex q).2).preimage
    (measurable_pi_apply (ofLex q).1)

private lemma measurable_infiniteOffspringCandidates {N : ℕ} :
    Measurable (fun batch : GenerationBatch N =>
      infiniteOffspringCandidates batch) := by
  rw [measurable_set_iff]
  intro q
  exact infiniteOffspringCandidate_mem_measurable q

/-- The complete candidate-position family is measurable in both the
ranked input configuration and the generation batch. -/
private theorem measurable_infiniteOffspringPosition {N : ℕ} :
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

private theorem measurable_totalizedInfiniteOffspringFirstN {N : ℕ} :
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
private theorem totalizedInfiniteOffspringFirstN_eq_infiniteOffspringFirstN
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

private lemma measurable_totalizedInfiniteOffspringRankOption_eq_some
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

private lemma measurable_totalizedInfiniteOffspringRankOption_eq_none
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

private theorem measurable_totalizedInfiniteOffspringRankLabel {N : ℕ}
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

private theorem measurable_totalizedInfiniteOffspringTransition {N : ℕ} :
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
private theorem totalizedInfiniteOffspringTransition_eq_of_good {N : ℕ}
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

private theorem fallbackGenerationBatch_repairable (N : ℕ) :
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

private lemma fallbackOffspringStep_isOrderedBy :
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

private lemma fallbackGenerationBatch_orderedFirst {N : ℕ} :
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
