/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Sibling
import Probability.BranchingRandomWalk.Restart.FirstSplit.BranchingProperty
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Law

/-!
# Recursive pre-sampled continuation siblings

At every selected-path split, the first selected child supplies one growth trial and
the second selected child continues the selected path.  The decomposition
is defined on the complete pre-sampled tree, whether or not the current growth
trial succeeds.  Under almost-sure finite split completion, the branching
property makes this decomposition an independent pair of full descendant
fields.  The finite all-failure event therefore has an exact product law.

This is the retrospective candidate construction for continuation siblings in
finite branching trials. It proves
the candidate event law; it does not identify the retrospectively restarted
population with an adapted selected BRW process.

## Public declarations

On finite first-split completion, the two sibling descendant fields \(U_1\)
and \(U_2\) have the product branching law. If one growth trial succeeds
with probability \(p\), the recursively defined all-failure events \(A_k\)
satisfy

\[\operatorname{Law}(U_1,U_2)=\nu\otimes\nu,\qquad
  \mathbb P(A_{k+1})=(1-p)\mathbb P(A_k)=(1-p)^{k+1}.\]

- `selectedPopulationFirstSplitSubtrees`,
  `selectedPopulationFirstSplitSubtrees_measurable`, and
  `selectedPopulationFirstSplitSubtrees_map_eq_product`: define the two
  totalized sibling descendant fields and identify their law with the product
  law under finite first-split completion.
- `Restart.SelectedPath.GrowthTrial.recursiveFailure`, `Restart.SelectedPath.GrowthTrial.recursiveFailure_measurable`,
  `Restart.SelectedPath.GrowthTrial.measure_recursiveFailure_succ`, and
  `Restart.SelectedPath.GrowthTrial.measure_recursiveFailure_eq_pow`: define the recursive all-failure
  event and show its probability is the corresponding power of the
  single-trial failure probability.
-/

open MeasureTheory ProbabilityTheory

section

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial

open ProbabilityTheory.BranchingProcess (offspringFieldLaw)

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
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ,
      selectedPopulationSplitCompletion R ω ≠ ⊤) :
    (offspringFieldLaw μ).map (selectedPopulationFirstSplitSubtrees R) =
      Measure.infinitePi (fun _ : Fin 2 => offspringFieldLaw μ) := by
  let ν := offspringFieldLaw μ
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

/-- The growth-trial recursion fails at its current growth trial and then
continues in the second selected sibling's pre-sampled descendant field.
Every future continuation field is defined before any earlier success outcome is
examined. -/
def recursiveFailure
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (duration lower upper : ℕ) :
    ℕ → Set (Mark α (Step α X))
  | 0 => Set.univ
  | k + 1 =>
      {ω | ¬ growthTrialSuccess growthSelection lower upper duration
          ((selectedPopulationFirstSplitSubtrees splitSelection ω) 0) ∧
        (selectedPopulationFirstSplitSubtrees splitSelection ω) 1 ∈
          Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection
            duration lower upper k}

theorem recursiveFailure_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (duration lower upper : ℕ) :
    ∀ k, MeasurableSet
      (Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection
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
          children ω 1 ∈ Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection
            growthSelection duration lower upper k})
      have hfail : MeasurableSet
          {ω | ¬ growthTrialSuccess growthSelection lower upper duration
            (children ω 0)} :=
        hsuccess.compl.preimage ((measurable_pi_apply 0).comp hchildren)
      have hcontinuation : MeasurableSet
          {ω | children ω 1 ∈ Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection
            growthSelection duration lower upper k} :=
        ih.preimage ((measurable_pi_apply 1).comp hchildren)
      exact hfail.inter hcontinuation

/-- One recursive continuation step splits into independent first-child and
second-child events. -/
theorem measure_recursiveFailure_succ
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (duration lower upper k : ℕ)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ,
      selectedPopulationSplitCompletion splitSelection ω ≠ ⊤) :
    offspringFieldLaw μ
        (Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection
          duration lower upper (k + 1)) =
      offspringFieldLaw μ
        {ω | ¬ growthTrialSuccess growthSelection lower upper duration ω} *
        offspringFieldLaw μ
          (Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection
            duration lower upper k) := by
  let ν := offspringFieldLaw μ
  let children := selectedPopulationFirstSplitSubtrees splitSelection
  let failedTrial : Set (Mark α (Step α X)) :=
    {ω | ¬ growthTrialSuccess growthSelection lower upper duration ω}
  let continuationFailure : Set (Mark α (Step α X)) :=
    Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection duration lower upper k
  let pairFailure : Set (Fin 2 → Mark α (Step α X)) :=
    {v | v 0 ∈ failedTrial ∧ v 1 ∈ continuationFailure}
  have hsuccess : MeasurableSet
      {ω : Mark α (Step α X) |
        growthTrialSuccess growthSelection lower upper duration ω} := by
    exact (generationFiltration (M := Step α X) |>.le duration) _
      (growthTrialSuccess_measurable growthSelection hgrowth
        lower upper duration)
  have hfailed : MeasurableSet failedTrial := by
    exact hsuccess.compl
  have hcontinuation : MeasurableSet continuationFailure :=
    (Restart.SelectedPath.GrowthTrial.recursiveFailure_measurable splitSelection growthSelection
      hsplit hgrowth duration lower upper) k
  have hpair : MeasurableSet pairFailure := by
    change MeasurableSet
      ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial ∩
        (fun v => v 1) ⁻¹' continuationFailure)
    exact (hfailed.preimage (measurable_pi_apply 0)).inter
      (hcontinuation.preimage (measurable_pi_apply 1))
  have hmap := selectedPopulationFirstSplitSubtrees_map_eq_product
    μ splitSelection hsplit hfinite
  have hevent :
      Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection
          duration lower upper (k + 1) = children ⁻¹' pairFailure := by
    ext ω
    simp [Restart.SelectedPath.GrowthTrial.recursiveFailure, children, pairFailure,
      failedTrial, continuationFailure]
  have hpairIndep : IndepFun
      (fun v : Fin 2 → Mark α (Step α X) => v 0)
      (fun v => v 1)
      (Measure.infinitePi (fun _ : Fin 2 => ν)) := by
    exact (iIndepFun_infinitePi
      (P := fun _ : Fin 2 => ν) (X := fun _ => id)
      (fun _ => measurable_id)).indepFun (by decide)
  have hpairFactor := hpairIndep.measure_inter_preimage_eq_mul
    failedTrial continuationFailure hfailed hcontinuation
  have hfailedMarginal :
      (Measure.infinitePi (fun _ : Fin 2 => ν))
          ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial) =
        ν failedTrial := by
    rw [← Measure.map_apply (measurable_pi_apply 0) hfailed]
    exact congrArg (fun Q : Measure (Mark α (Step α X)) => Q failedTrial)
      (RootIndexed.stepFieldLaw_root_marginal μ 0)
  have hcontinuationMarginal :
      (Measure.infinitePi (fun _ : Fin 2 => ν))
          ((fun v : Fin 2 → Mark α (Step α X) => v 1) ⁻¹' continuationFailure) =
        ν continuationFailure := by
    rw [← Measure.map_apply (measurable_pi_apply 1) hcontinuation]
    exact congrArg (fun Q : Measure (Mark α (Step α X)) => Q continuationFailure)
      (RootIndexed.stepFieldLaw_root_marginal μ 1)
  calc
    ν (Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection
        duration lower upper (k + 1)) = ν (children ⁻¹' pairFailure) := by
      rw [hevent]
    _ = (Measure.infinitePi (fun _ : Fin 2 => ν)) pairFailure := by
      rw [← Measure.map_apply (selectedPopulationFirstSplitSubtrees_measurable
        splitSelection hsplit) hpair]
      exact congrArg (fun Q : Measure (Fin 2 → Mark α (Step α X)) => Q pairFailure)
        hmap
    _ = ν failedTrial * ν continuationFailure := by
      calc
        (Measure.infinitePi (fun _ : Fin 2 => ν)) pairFailure =
            (Measure.infinitePi (fun _ : Fin 2 => ν))
              ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial ∩
                (fun v => v 1) ⁻¹' continuationFailure) := rfl
        _ = (Measure.infinitePi (fun _ : Fin 2 => ν))
              ((fun v : Fin 2 → Mark α (Step α X) => v 0) ⁻¹' failedTrial) *
            (Measure.infinitePi (fun _ : Fin 2 => ν))
              ((fun v : Fin 2 → Mark α (Step α X) => v 1) ⁻¹' continuationFailure) :=
                hpairFactor
        _ = ν failedTrial * ν continuationFailure := by
          rw [hfailedMarginal, hcontinuationMarginal]

/-- The probability that the first `k` recursively pre-sampled successive
growth trials all fail is the `k`th power of the one-trial failure probability. -/
theorem measure_recursiveFailure_eq_pow
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (duration lower upper : ℕ)
    (hfinite : ∀ᵐ ω ∂offspringFieldLaw μ,
      selectedPopulationSplitCompletion splitSelection ω ≠ ⊤) :
    ∀ k, offspringFieldLaw μ
        (Restart.SelectedPath.GrowthTrial.recursiveFailure splitSelection growthSelection
          duration lower upper k) =
      (offspringFieldLaw μ
        {ω | ¬ growthTrialSuccess growthSelection lower upper duration ω}) ^ k := by
  intro k
  induction k with
  | zero => simp [Restart.SelectedPath.GrowthTrial.recursiveFailure]
  | succ k ih =>
      rw [Restart.SelectedPath.GrowthTrial.measure_recursiveFailure_succ μ splitSelection
        growthSelection hsplit hgrowth duration lower upper k hfinite, ih,
        pow_succ']

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial

end
