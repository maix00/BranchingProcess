/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.Infinite
public import Probability.BranchingRandomWalk.Step.Field.FiniteWeight
public import Probability.BranchingRandomWalk.Step.Ordering.Support
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Stationary generation environments for finite selection

Each generation consists of one independent offspring mark for each current
rank. Generations themselves form an i.i.d. sequence. The one-sided shift is
measure-preserving, and the normalization and nonempty-offspring
assumptions make every generation a good transition almost surely.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open scoped ENNReal

/-- The offspring marks assigned to the `N` ranked parents in one generation. -/
abbrev GenerationBatch (N : ℕ) := Fin N → Step ℕ ℝ

/-- The law of a batch of independent offspring marks, one per parent. -/
noncomputable def generationBatchLaw (μ : Measure (Step ℕ ℝ)) (N : ℕ) :
    Measure (GenerationBatch N) :=
  Measure.pi (fun _ : Fin N => μ)

/-- The law of the sequence of independent generation batches. -/
noncomputable def generationEnvironmentLaw
    (μ : Measure (Step ℕ ℝ)) (N : ℕ) : Measure (ℕ → GenerationBatch N) :=
  Measure.infinitePi (fun _ : ℕ => generationBatchLaw μ N)

/-- Shift a generation environment forward by one generation. -/
def generationEnvironmentShift {N : ℕ}
    (ω : ℕ → GenerationBatch N) : ℕ → GenerationBatch N :=
  fun n => ω (n + 1)

instance generationBatchLaw.isProbabilityMeasure
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    IsProbabilityMeasure (generationBatchLaw μ N) := by
  unfold generationBatchLaw
  infer_instance

theorem generationEnvironmentLaw_isProbability
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    IsProbabilityMeasure (generationEnvironmentLaw μ N) := by
  unfold generationEnvironmentLaw
  infer_instance

theorem generationBatchLaw_parent_marginal
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] {N : ℕ} (i : Fin N) :
    (generationBatchLaw μ N).map (fun batch => batch i) = μ := by
  exact (measurePreserving_eval (fun _ : Fin N => μ) i).map_eq

theorem generationBatchLaw_parent_independent
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    iIndepFun (fun i (batch : GenerationBatch N) => batch i)
      (generationBatchLaw μ N) := by
  unfold generationBatchLaw
  exact iIndepFun_pi (X := fun _ : Fin N => id)
    (fun _ => aemeasurable_id)

theorem generationEnvironmentLaw_shift_measurePreserving
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    MeasurePreserving (generationEnvironmentShift :
      (ℕ → GenerationBatch N) → (ℕ → GenerationBatch N))
      (generationEnvironmentLaw μ N) (generationEnvironmentLaw μ N) := by
  refine ⟨?_, ?_⟩
  · rw [measurable_pi_iff]
    intro n
    exact measurable_pi_apply (n + 1)
  · rw [show generationEnvironmentShift =
        (fun ω n => ω (Nat.succ n)) by
          funext ω n
          rfl]
    unfold generationEnvironmentLaw
    exact Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => generationBatchLaw μ N) Nat.succ_injective

private lemma ae_generationBatch_finiteWeight
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (i : Fin N) :
    ∀ᵐ batch ∂generationBatchLaw μ N,
      totalChildWeight (batch i) ≠ ∞ := by
  have hμ : ∀ᵐ ξ ∂μ, totalChildWeight ξ ≠ ∞ := by
    simpa [totalPotentialWeight_real_neg_one] using
      hboundary.ae_totalPotentialWeight_ne_top realPotential μ
  have hmap := generationBatchLaw_parent_marginal μ i
  have hmapAE : ∀ᵐ ξ ∂(generationBatchLaw μ N).map
      (fun batch => batch i), totalChildWeight ξ ≠ ∞ := by
    rw [hmap]
    exact hμ
  have hset : MeasurableSet
      {ξ : Step ℕ ℝ | totalChildWeight ξ ≠ ∞} := by
    change MeasurableSet
      ((totalChildWeight : Step ℕ ℝ → ENNReal) ⁻¹' ({∞}ᶜ))
    exact totalChildWeight_measurable (MeasurableSet.singleton ∞).compl
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    hset).1 hmapAE

private lemma ae_generationBatch_nonempty
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnonempty : μ nonemptySupport = 1)
    (N : ℕ) (i : Fin N) :
    ∀ᵐ batch ∂generationBatchLaw μ N, batch i ∈ nonemptySupport := by
  have hmap := generationBatchLaw_parent_marginal μ i
  have hμ : ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
    exact (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
      (by simpa using hnonempty)
  have hmapAE : ∀ᵐ ξ ∂(generationBatchLaw μ N).map
      (fun batch => batch i), ξ ∈ nonemptySupport := by
    rw [hmap]
    exact hμ
  have hset : MeasurableSet {ξ : Step ℕ ℝ | ξ ∈ nonemptySupport} := by
    simpa using nonemptySupport_measurable
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    hset).1 hmapAE

/-- A batch drawn from the product offspring law is a good transition almost
surely under boundary normalization and almost-surely nonempty offspring. -/
theorem generationBatchLaw_ae_isGoodInfiniteOffspringBatch
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) (N : ℕ) :
    ∀ᵐ batch ∂generationBatchLaw μ N,
      IsGoodInfiniteOffspringBatch batch := by
  have hfinite : ∀ᵐ batch ∂generationBatchLaw μ N,
      ∀ i, totalChildWeight (batch i) ≠ ∞ := by
    exact ae_all_iff.2 (ae_generationBatch_finiteWeight μ hboundary N)
  have hchildren : ∀ᵐ batch ∂generationBatchLaw μ N,
      ∀ i, batch i ∈ nonemptySupport := by
    exact ae_all_iff.2 (ae_generationBatch_nonempty μ hnonempty N)
  filter_upwards [hfinite, hchildren] with batch hfinite hchildren
  refine ⟨hfinite, ?_⟩
  apply infiniteOffspringCandidates_hasFiniteSubset_card
  intro i
  obtain ⟨j, hj⟩ := hchildren i
  exact ⟨j, hj⟩

/-- At each fixed generation, the environment row has the product law of
the offspring marks. -/
theorem generationEnvironmentLaw_generation_marginal
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N n : ℕ) :
    (generationEnvironmentLaw μ N).map (fun ω => ω n) =
      generationBatchLaw μ N := by
  unfold generationEnvironmentLaw
  exact Measure.infinitePi_map_eval (fun _ : ℕ => generationBatchLaw μ N) n

/-- Distinct generation batches are independent under the product environment
law. Together with the marginal law, this records the iid block environment
used in the speed argument. -/
theorem generationEnvironmentLaw_generations_independent
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    iIndepFun (fun n (ω : ℕ → GenerationBatch N) => ω n)
      (generationEnvironmentLaw μ N) := by
  unfold generationEnvironmentLaw
  exact iIndepFun_infinitePi (X := fun _ : ℕ => id)
    (fun _ => measurable_id)

/-- Almost surely, every generation in the pre-sampled environment is a good
countable-offspring transition. -/
theorem generationEnvironmentLaw_ae_allGood
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) (N : ℕ) :
    ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∀ n, IsGoodInfiniteOffspringBatch (ω n) := by
  apply ae_all_iff.2
  intro n
  have hrow := generationBatchLaw_ae_isGoodInfiniteOffspringBatch
    μ hboundary hnonempty N
  have hmapAE : ∀ᵐ batch ∂(generationEnvironmentLaw μ N).map
      (fun ω => ω n), IsGoodInfiniteOffspringBatch batch := by
    rw [generationEnvironmentLaw_generation_marginal μ N n]
    exact hrow
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable hmapAE

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
