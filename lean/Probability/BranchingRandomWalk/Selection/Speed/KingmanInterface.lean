/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.Speed.ErgodicEnvironment
public import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
public import Probability.BranchingRandomWalk.Selection.NSelection.Totalized
public import Probability.Ergodic.Kingman.Core

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

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Speed

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

/-- Apply the ergodic Kingman theorem to the repaired finite-selection array.
The two analytic inputs are stated explicitly: integrability of every block
length and a uniform lower bound on normalized expected block values. -/
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
  exact ProbabilityTheory.tendsto_kingman_ergodic
    (generationEnvironmentShift_ergodic μ N)
    (repairedInfiniteSelection_isSubadditiveCocycle hN) hint hbdd

end ProbabilityTheory.BranchingRandomWalk.Selection.Speed

end
