/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.SiblingTrial
import Probability.Sequence.IID
import Probability.BranchingRandomWalk.Restart.FirstSplit.BranchingProperty
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Law

/-!
# Recursive pre-sampled reserve siblings

At every reserve split, the first selected child supplies one growth trial and
the second selected child supplies the next reserve tree.  The decomposition
is defined on the complete pre-sampled tree, whether or not the current growth
trial succeeds.  Under almost-sure finite split completion, the branching
property makes this decomposition an independent pair of full descendant
fields.  The finite all-failure event therefore has an exact product law.

This is the retrospective candidate construction from the thesis.  It proves
the candidate event law; it does not identify the retrospectively restarted
population with an adapted killed process.
-/

open MeasureTheory ProbabilityTheory

section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

/-- The two full descendant fields at the selected population's first split.
The vector is totalized on samples without a finite split; such samples are
null under the termination hypothesis used below. -/
noncomputable def selectedPopulationFirstSplitSubtrees
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) :
    Mark α (Step α X) → Fin 2 → Mark α (Step α X) :=
  selectedSubtreeStepFieldVector (selectedPopulationFirstSplitRoots R)

theorem selectedPopulationFirstSplitSubtrees_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    Measurable (selectedPopulationFirstSplitSubtrees R) := by
  let roots := selectedPopulationFirstSplitRoots R
  let hσ := selectedPopulationSplitCompletion_isStoppingTime R hR
  have hrootMeas : Measurable roots := by
    intro s hs
    have hpre : roots ⁻¹' s =
        ⋃ r : {r : Fin 2 → TreeNode α // r ∈ s}, {ω | roots ω = r.1} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · intro hω
        exact ⟨⟨roots ω, hω⟩, rfl⟩
      · rintro ⟨r, hr⟩
        simp [hr, r.2]
    rw [hpre]
    apply MeasurableSet.iUnion
    intro r
    exact hσ.measurableSpace_le _
      (selectedPopulationFirstSplitRoots_fiber_measurable R hR r.1)
  exact selectedSubtreeStepFieldVector_measurable_of_measurable
    roots hrootMeas (Set.to_countable _)

/-- If the first selected split is finite almost surely, its two sibling
subtrees have the full product branching law.  The finite-split branching
identity is applied on the observable completion `σ`; no stopping-time claim
is made for the raw look-ahead time `τ`. -/
theorem selectedPopulationFirstSplitSubtrees_map_eq_product
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hfinite : ∀ᵐ ω ∂stepFieldLaw μ,
      selectedPopulationSplitCompletion R ω ≠ ⊤) :
    (stepFieldLaw μ).map (selectedPopulationFirstSplitSubtrees R) =
      Measure.infinitePi (fun _ : Fin 2 => stepFieldLaw μ) := by
  let ν := stepFieldLaw μ
  let σ := selectedPopulationSplitCompletion R
  let finite : Set (Mark α (Step α X)) := {ω | σ ω ≠ ⊤}
  have hfiniteSet : finite =ᵐ[ν] Set.univ := by
    filter_upwards [hfinite] with ω hω
    change (σ ω ≠ ⊤) = True
    exact propext ⟨fun _ => trivial, fun _ => hω⟩
  have hpreimage (B : Set (Fin 2 → Mark α (Step α X))) :
      (finite ∩ selectedPopulationFirstSplitSubtrees R ⁻¹' B) =ᵐ[ν]
        selectedPopulationFirstSplitSubtrees R ⁻¹' B := by
    filter_upwards [hfinite] with ω hω
    change ((σ ω ≠ ⊤) ∧
      selectedPopulationFirstSplitSubtrees R ω ∈ B) =
        (selectedPopulationFirstSplitSubtrees R ω ∈ B)
    exact propext (and_iff_right hω)
  have hmap : Measurable (selectedPopulationFirstSplitSubtrees R) :=
    selectedPopulationFirstSplitSubtrees_measurable R hR
  ext B hB
  rw [Measure.map_apply hmap hB]
  have hfactor := selectedPopulation_firstSplit_subtree_vector_factorization
    μ R hR Set.univ B (by simp) hB
  have hfactor' :
      ν (finite ∩ selectedPopulationFirstSplitSubtrees R ⁻¹' B) =
        ν finite * (Measure.infinitePi (fun _ : Fin 2 => ν)) B := by
    simpa [ν, σ, finite, selectedPopulationFirstSplitSubtrees] using hfactor
  have hleft : ν (finite ∩ selectedPopulationFirstSplitSubtrees R ⁻¹' B) =
      ν (selectedPopulationFirstSplitSubtrees R ⁻¹' B) :=
    measure_congr (hpreimage B)
  have hmass : ν finite = 1 := by
    rw [measure_congr hfiniteSet, measure_univ]
  rw [hleft, hmass, one_mul] at hfactor'
  exact hfactor'

/-- The reserve recursion fails at its current growth trial and then
continues in the second selected sibling's pre-sampled descendant field.
Every future reserve field is defined before any earlier success outcome is
examined. -/
def recursiveReserveFailure
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (duration lower upper : ℕ) :
    ℕ → Set (Mark α (Step α X))
  | 0 => Set.univ
  | k + 1 =>
      {ω | ¬ growthTrialSuccess growthSelection lower upper duration
          ((selectedPopulationFirstSplitSubtrees splitSelection ω) 0) ∧
        (selectedPopulationFirstSplitSubtrees splitSelection ω) 1 ∈
          recursiveReserveFailure splitSelection growthSelection
            duration lower upper k}

theorem recursiveReserveFailure_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (duration lower upper : ℕ) :
    ∀ k, MeasurableSet
      (recursiveReserveFailure splitSelection growthSelection
        duration lower upper k) := by
  let children := selectedPopulationFirstSplitSubtrees splitSelection
  have hchildren : Measurable children :=
    selectedPopulationFirstSplitSubtrees_measurable splitSelection hsplit
  have hsuccess : MeasurableSet
      {ω : Mark α (Step α X) |
        growthTrialSuccess growthSelection lower upper duration ω} := by
    exact (generationFiltration (M := Step α X) |>.le duration) _
      (growthTrialSuccess_measurable growthSelection hgrowth
        lower upper duration)
  intro k
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih =>
      change MeasurableSet
        ({ω | ¬ growthTrialSuccess growthSelection lower upper duration
            (children ω 0) ∧
          children ω 1 ∈ recursiveReserveFailure splitSelection
            growthSelection duration lower upper k})
      have hfail : MeasurableSet
          {ω | ¬ growthTrialSuccess growthSelection lower upper duration
            (children ω 0)} :=
        hsuccess.compl.preimage ((measurable_pi_apply 0).comp hchildren)
      have hreserve : MeasurableSet
          {ω | children ω 1 ∈ recursiveReserveFailure splitSelection
            growthSelection duration lower upper k} :=
        ih.preimage ((measurable_pi_apply 1).comp hchildren)
      exact hfail.inter hreserve

/-- One recursive reserve step splits into independent first-child and
second-child events. -/
theorem measure_recursiveReserveFailure_succ
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (duration lower upper k : ℕ)
    (hfinite : ∀ᵐ ω ∂stepFieldLaw μ,
      selectedPopulationSplitCompletion splitSelection ω ≠ ⊤) :
    stepFieldLaw μ
        (recursiveReserveFailure splitSelection growthSelection
          duration lower upper (k + 1)) =
      stepFieldLaw μ
        {ω | ¬ growthTrialSuccess growthSelection lower upper duration ω} *
        stepFieldLaw μ
          (recursiveReserveFailure splitSelection growthSelection
            duration lower upper k) := by
  let ν := stepFieldLaw μ
  let children := selectedPopulationFirstSplitSubtrees splitSelection
  let failedTrial : Set (Mark α (Step α X)) :=
    {ω | ¬ growthTrialSuccess growthSelection lower upper duration ω}
  let reserveFailure : Set (Mark α (Step α X)) :=
    recursiveReserveFailure splitSelection growthSelection duration lower upper k
  let pairFailure : Set (Fin 2 → Mark α (Step α X)) :=
    {v | v 0 ∈ failedTrial ∧ v 1 ∈ reserveFailure}
  have hsuccess : MeasurableSet
      {ω : Mark α (Step α X) |
        growthTrialSuccess growthSelection lower upper duration ω} := by
    exact (generationFiltration (M := Step α X) |>.le duration) _
      (growthTrialSuccess_measurable growthSelection hgrowth
        lower upper duration)
  have hfailed : MeasurableSet failedTrial := by
    exact hsuccess.compl
  have hreserve : MeasurableSet reserveFailure :=
    (recursiveReserveFailure_measurable splitSelection growthSelection
      hsplit hgrowth duration lower upper) k
  have hpair : MeasurableSet pairFailure := by
    change MeasurableSet
      ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial ∩
        (fun v => v 1) ⁻¹' reserveFailure)
    exact (hfailed.preimage (measurable_pi_apply 0)).inter
      (hreserve.preimage (measurable_pi_apply 1))
  have hmap := selectedPopulationFirstSplitSubtrees_map_eq_product
    μ splitSelection hsplit hfinite
  have hevent :
      recursiveReserveFailure splitSelection growthSelection
          duration lower upper (k + 1) = children ⁻¹' pairFailure := by
    ext ω
    simp [recursiveReserveFailure, children, pairFailure,
      failedTrial, reserveFailure]
  have hpairIndep : IndepFun
      (fun v : Fin 2 → Mark α (Step α X) => v 0)
      (fun v => v 1)
      (Measure.infinitePi (fun _ : Fin 2 => ν)) := by
    exact (iIndepFun_infinitePi
      (P := fun _ : Fin 2 => ν) (X := fun _ => id)
      (fun _ => measurable_id)).indepFun (by decide)
  have hpairFactor := hpairIndep.measure_inter_preimage_eq_mul
    failedTrial reserveFailure hfailed hreserve
  have hfailedMarginal :
      (Measure.infinitePi (fun _ : Fin 2 => ν))
          ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial) =
        ν failedTrial := by
    rw [← Measure.map_apply (measurable_pi_apply 0) hfailed]
    exact congrArg (fun Q : Measure (Mark α (Step α X)) => Q failedTrial)
      (RootIndexed.stepFieldLaw_root_marginal μ 0)
  have hreserveMarginal :
      (Measure.infinitePi (fun _ : Fin 2 => ν))
          ((fun v : Fin 2 → Mark α (Step α X) => v 1) ⁻¹' reserveFailure) =
        ν reserveFailure := by
    rw [← Measure.map_apply (measurable_pi_apply 1) hreserve]
    exact congrArg (fun Q : Measure (Mark α (Step α X)) => Q reserveFailure)
      (RootIndexed.stepFieldLaw_root_marginal μ 1)
  calc
    ν (recursiveReserveFailure splitSelection growthSelection
        duration lower upper (k + 1)) = ν (children ⁻¹' pairFailure) := by
      rw [hevent]
    _ = (Measure.infinitePi (fun _ : Fin 2 => ν)) pairFailure := by
      rw [← Measure.map_apply (selectedPopulationFirstSplitSubtrees_measurable
        splitSelection hsplit) hpair]
      exact congrArg (fun Q : Measure (Fin 2 → Mark α (Step α X)) => Q pairFailure)
        hmap
    _ = ν failedTrial * ν reserveFailure := by
      calc
        (Measure.infinitePi (fun _ : Fin 2 => ν)) pairFailure =
            (Measure.infinitePi (fun _ : Fin 2 => ν))
              ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial ∩
                (fun v => v 1) ⁻¹' reserveFailure) := rfl
        _ = (Measure.infinitePi (fun _ : Fin 2 => ν))
              ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial) *
            (Measure.infinitePi (fun _ : Fin 2 => ν))
              ((fun v : Fin 2 → Mark α (Step α X) => v 1) ⁻¹' reserveFailure) :=
                hpairFactor
        _ = ν failedTrial * ν reserveFailure := by
          rw [hfailedMarginal, hreserveMarginal]

/-- The probability that the first `k` recursively pre-sampled backup
trials all fail is the `k`th power of the one-trial failure probability. -/
theorem measure_recursiveReserveFailure_eq_pow
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (duration lower upper : ℕ)
    (hfinite : ∀ᵐ ω ∂stepFieldLaw μ,
      selectedPopulationSplitCompletion splitSelection ω ≠ ⊤) :
    ∀ k, stepFieldLaw μ
        (recursiveReserveFailure splitSelection growthSelection
          duration lower upper k) =
      (stepFieldLaw μ
        {ω | ¬ growthTrialSuccess growthSelection lower upper duration ω}) ^ k := by
  intro k
  induction k with
  | zero => simp [recursiveReserveFailure]
  | succ k ih =>
      rw [measure_recursiveReserveFailure_succ μ splitSelection
        growthSelection hsplit hgrowth duration lower upper k hfinite, ih,
        pow_succ']

end ProbabilityTheory.BranchingRandomWalk

end
