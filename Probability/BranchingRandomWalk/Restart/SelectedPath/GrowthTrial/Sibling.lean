/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Lineage
/-!
# A growth trial and its continuation sibling

At the observable completion of a first split, the first selected child can
run a finite growth trial while the second selected child gives the continuation
subtree.  Their complete descendant fields have the product branching law,
independently of the stopped domain past.  The split mark is allowed to have
any finite selected offspring set of cardinality at least two.

## Public declarations

For a stopped-past event \(A\), a first-sibling growth event \(G\), and a
second-sibling continuation event \(R\), the branching property gives

\[\mathbb P(A\cap G\cap R)=\mathbb P(A)\,\mathbb P(G)\,\mathbb P(R).\]

`siblingField_factorization`
factors the joint event of a measurable stopped past, a finite growth-trial
success in the first-child subtree, and an arbitrary measurable event in the
continuation-child subtree. Its probability is the stopped-past probability
times the two corresponding one-subtree probabilities, using independence of
the two descendant fields under the product branching law.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

theorem siblingField_factorization
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.PreSampledLineages Root Trial α X)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplitSelection : Measurable splitSelection.select)
    (hgrowthSelection : Measurable growthSelection.select)
    (splitMark : Set (Step α X)) (hsplit : MeasurableSet splitMark)
    (hsplitMark : splitMark ⊆ splitBy splitSelection)
    (r : Root) (i : Trial) (duration lower upper : ℕ)
    (A : Set (RootIndexed.StepField Root α X))
    (hA : MeasurableSet[
      (lineages.sigma_isStoppingTime splitMark hsplit r i).measurableSpace] A)
    (B : Set (TreeNode α → Step α X)) (hB : MeasurableSet B) :
    let σ := lineages.sigma splitMark r i
    let roots := sigmaGrowthTrialAndContinuationRoots lineages splitSelection splitMark r i
    let trialEvent := {ω | growthTrialSuccess growthSelection lower upper
      duration (fun v => ω (roots ω 0).1 ((roots ω 0).2 ++ v))}
    let continuationEvent := {ω | (fun v => ω (roots ω 1).1 ((roots ω 1).2 ++ v)) ∈ B}
    RootIndexed.stepFieldLaw (Root := Root) μ
        (((A ∩ {ω | σ ω ≠ ⊤}) ∩ trialEvent) ∩ continuationEvent) =
      RootIndexed.stepFieldLaw (Root := Root) μ
          (A ∩ {ω | σ ω ≠ ⊤}) *
        ProbabilityTheory.BranchingProcess.offspringFieldLaw μ
          {ω | growthTrialSuccess growthSelection lower upper duration ω} *
        ProbabilityTheory.BranchingProcess.offspringFieldLaw μ B := by
  classical
  dsimp only
  let σ := lineages.sigma splitMark r i
  let roots := sigmaGrowthTrialAndContinuationRoots lineages splitSelection splitMark r i
  let trialSet : Set (Mark α (Step α X)) :=
    {ω | growthTrialSuccess growthSelection lower upper duration ω}
  let pairSet : Set (Fin 2 → TreeNode α → Step α X) :=
    {v | v 0 ∈ trialSet ∧ v 1 ∈ B}
  have hσ : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) σ :=
    lineages.sigma_isStoppingTime splitMark hsplit r i
  have htrialFiltration : MeasurableSet[generationFiltration
      (M := Step α X) duration] trialSet := by
    exact growthTrialSuccess_measurable growthSelection hgrowthSelection
      lower upper duration
  have htrial : MeasurableSet trialSet :=
    (generationFiltration (M := Step α X) |>.le duration) _ htrialFiltration
  have hpair : MeasurableSet pairSet := by
    change MeasurableSet
      ((fun v : Fin 2 → TreeNode α → Step α X => v 0) ⁻¹' trialSet ∩
        (fun v : Fin 2 → TreeNode α → Step α X => v 1) ⁻¹' B)
    exact (htrial.preimage (measurable_pi_apply 0)).inter
      (hB.preimage (measurable_pi_apply 1))
  have hvector := siblingField_factorization_on_finite lineages μ
    splitSelection hsplitSelection splitMark hsplit hsplitMark r i A pairSet hA hpair
  have hindep : IndepFun (fun v : Fin 2 → TreeNode α → Step α X => v 0)
      (fun v => v 1)
      (RootIndexed.stepFieldLaw (Root := Fin 2) μ) := by
    unfold RootIndexed.stepFieldLaw
    exact (iIndepFun_infinitePi
      (P := fun _ : Fin 2 => ProbabilityTheory.BranchingProcess.offspringFieldLaw μ)
      (X := fun _ => id) (fun _ => measurable_id)).indepFun (by decide)
  have hpairProduct := hindep.measure_inter_preimage_eq_mul
    trialSet B htrial hB
  have htrialMarginal :
      RootIndexed.stepFieldLaw (Root := Fin 2) μ
          ((fun v : Fin 2 → TreeNode α → Step α X => v 0) ⁻¹' trialSet) =
        ProbabilityTheory.BranchingProcess.offspringFieldLaw μ trialSet := by
    rw [← Measure.map_apply (measurable_pi_apply 0) htrial]
    exact congrArg (fun Q : Measure (TreeNode α → Step α X) => Q trialSet)
      (RootIndexed.stepFieldLaw_root_marginal μ 0)
  have hcontinuationMarginal :
      RootIndexed.stepFieldLaw (Root := Fin 2) μ
          ((fun v : Fin 2 → TreeNode α → Step α X => v 1) ⁻¹' B) =
        ProbabilityTheory.BranchingProcess.offspringFieldLaw μ B := by
    rw [← Measure.map_apply (measurable_pi_apply 1) hB]
    exact congrArg (fun Q : Measure (TreeNode α → Step α X) => Q B)
      (RootIndexed.stepFieldLaw_root_marginal μ 1)
  have hpairMeasure :
      RootIndexed.stepFieldLaw (Root := Fin 2) μ pairSet =
        ProbabilityTheory.BranchingProcess.offspringFieldLaw μ trialSet *
          ProbabilityTheory.BranchingProcess.offspringFieldLaw μ B := by
    calc
      RootIndexed.stepFieldLaw (Root := Fin 2) μ pairSet =
          RootIndexed.stepFieldLaw (Root := Fin 2) μ
            ((fun v : Fin 2 → TreeNode α → Step α X => v 0) ⁻¹' trialSet ∩
              (fun v : Fin 2 → TreeNode α → Step α X => v 1) ⁻¹' B) := rfl
      _ = RootIndexed.stepFieldLaw (Root := Fin 2) μ
            ((fun v : Fin 2 → TreeNode α → Step α X => v 0) ⁻¹' trialSet) *
          RootIndexed.stepFieldLaw (Root := Fin 2) μ
            ((fun v : Fin 2 → TreeNode α → Step α X => v 1) ⁻¹' B) := hpairProduct
      _ = ProbabilityTheory.BranchingProcess.offspringFieldLaw μ trialSet *
          ProbabilityTheory.BranchingProcess.offspringFieldLaw μ B := by
        rw [htrialMarginal, hcontinuationMarginal]
  have htrialRoot (ω : RootIndexed.StepField Root α X) :
      (RootIndexed.selectedSubtreeStepFieldVector roots ω) 0 =
        (fun v => ω (roots ω 0).1 ((roots ω 0).2 ++ v)) := by
    change (fun j v => ω (roots ω j).1 ((roots ω j).2 ++ v)) 0 = _
    rfl
  have hcontinuationRoot (ω : RootIndexed.StepField Root α X) :
      (RootIndexed.selectedSubtreeStepFieldVector roots ω) 1 =
        (fun v => ω (roots ω 1).1 ((roots ω 1).2 ++ v)) := by
    change (fun j v => ω (roots ω j).1 ((roots ω j).2 ++ v)) 1 = _
    rfl
  have hevent :
      ((A ∩ {ω | σ ω ≠ ⊤}) ∩
        {ω | growthTrialSuccess growthSelection lower upper duration
          (fun v => ω (roots ω 0).1 ((roots ω 0).2 ++ v))}) ∩
        {ω | (fun v => ω (roots ω 1).1 ((roots ω 1).2 ++ v)) ∈ B} =
      (A ∩ {ω | σ ω ≠ ⊤}) ∩
        RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' pairSet := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨⟨⟨hAω, hfinite⟩, htrialω⟩, hcontinuationω⟩
      refine ⟨⟨hAω, hfinite⟩, ?_⟩
      change (RootIndexed.selectedSubtreeStepFieldVector roots ω 0 ∈ trialSet ∧
        RootIndexed.selectedSubtreeStepFieldVector roots ω 1 ∈ B)
      rw [htrialRoot ω, hcontinuationRoot ω]
      exact ⟨htrialω, hcontinuationω⟩
    · rintro ⟨⟨hAω, hfinite⟩, hpairω⟩
      refine ⟨⟨⟨hAω, hfinite⟩, ?_⟩, ?_⟩
      · change (RootIndexed.selectedSubtreeStepFieldVector roots ω 0 ∈ trialSet ∧
          RootIndexed.selectedSubtreeStepFieldVector roots ω 1 ∈ B) at hpairω
        rw [htrialRoot ω, hcontinuationRoot ω] at hpairω
        exact hpairω.1
      · change (RootIndexed.selectedSubtreeStepFieldVector roots ω 0 ∈ trialSet ∧
          RootIndexed.selectedSubtreeStepFieldVector roots ω 1 ∈ B) at hpairω
        rw [htrialRoot ω, hcontinuationRoot ω] at hpairω
        exact hpairω.2
  rw [hevent, hvector]
  rw [hpairMeasure]
  rw [← mul_assoc]

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial

end
