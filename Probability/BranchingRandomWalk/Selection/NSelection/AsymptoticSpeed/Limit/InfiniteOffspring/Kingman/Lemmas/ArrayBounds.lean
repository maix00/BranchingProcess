/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.SubadditiveArray
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.Infinite
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Estimates for the repaired selection array

These statements are proof steps in the Kingman speed argument for the
repaired infinite-offspring selection array.

- `repairedGenerationBatchSeq` and `repairedGenerationBatchSeq_good`:
  the generation sequence after repair and its validity at every time.
- `measurable_infiniteOffspringBatchSlotZeroNorm` and
  `measurable_repairedInfiniteSelectionSubadditiveArray`: measurability of
  the generation envelope and repaired block array.
- `integrable_repairedInfiniteOffspringBatchSlotZeroNorm_at`: integrability
  of the repaired generation envelope under the environment law.
- `repairedInfiniteSelectionSubadditiveArray_eq_deterministic`: identifies
  the measurable repaired block array with the deterministic subadditive array.
- `repairedInfiniteSelectionSubadditiveArray_ae_abs_le_envelope`: almost
  surely, the absolute block value is bounded by the sum of the generation
  envelopes.
- `repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment`:
  the block array is integrable under the leftmost first-moment assumption.
- `repairedInfiniteSelection_normalizedIntegral_bddBelow_of_leftmostMoment`:
  the normalized expected block values are bounded below.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

/-- The finite-generation envelope is measurable in the offspring batch. -/
lemma measurable_infiniteOffspringBatchSlotZeroNorm {N : ℕ} (hN : 0 < N) :
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
private theorem integrable_infiniteOffspringBatchSlotZeroNorm {N : ℕ}
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
private theorem integrable_repairedInfiniteOffspringBatchSlotZeroNorm {N : ℕ}
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

/-- The generation sequence after repairing every batch in an environment. -/
noncomputable def repairedGenerationBatchSeq {N : ℕ}
    (ω : GenerationEnvironment N) : ℕ → GenerationBatch N :=
  fun t => repairGenerationBatch (ω t)

lemma repairedGenerationBatchSeq_good {N : ℕ}
    (ω : GenerationEnvironment N) :
    ∀ t, IsGoodInfiniteOffspringBatch (repairedGenerationBatchSeq ω t) := by
  intro t
  change IsRepairableBatch (repairGenerationBatch (ω t))
  exact repairGenerationBatch_repairable (ω t)

/-- The repaired block array is measurable in the generation environment. -/
lemma measurable_repairedInfiniteSelectionSubadditiveArray {N : ℕ}
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
lemma integrable_repairedInfiniteOffspringBatchSlotZeroNorm_at {N : ℕ}
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
lemma repairedInfiniteSelectionSubadditiveArray_eq_deterministic
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
lemma repairedInfiniteSelectionSubadditiveArray_ae_abs_le_envelope
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

/-- The block endpoint array is integrable under the one-step
leftmost-child moment condition and the ordered, nonempty offspring support.
The proof uses the deterministic sup-norm recursion, then integrates its
finite sum of generation envelopes. -/
lemma repairedInfiniteSelectionSubadditiveArray_integrable_of_leftmostMoment
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
lemma repairedInfiniteSelection_normalizedIntegral_bddBelow_of_leftmostMoment
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
end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
