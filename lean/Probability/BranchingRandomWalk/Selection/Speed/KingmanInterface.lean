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
      exact measurableSet_setOfPred.mpr <| h.ne measurable_const
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
      change MeasurableSet
        {batch : GenerationBatch N |
          (↑s : Set (InfiniteSlotLabel N)) ⊆
            infiniteOffspringCandidates batch ∧ s.card = N}
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
            simp
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
  · simpa [repairGenerationBatch, h] using h
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

end ProbabilityTheory.BranchingRandomWalk.Selection.Speed

end
