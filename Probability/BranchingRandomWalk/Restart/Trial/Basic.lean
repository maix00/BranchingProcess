/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
public import MeasureTheory.BranchingWalk.Step.Selection.Slot


/-!
# Finite selected-population growth trials

This module defines split marks and the event for a finite trial of the
recursively selected population. Ordered selected-slot operations belong to
`Combinatorics.Branching.Step.FiniteSelection`.

## Public declarations

* `splitBy R = {ξ | 2 ≤ (R ξ).card}` records binary split marks, with
  `splitBy_measurable` proving measurability.
* `growthTrialSuccess R lower upper duration ω` states that the endpoint
  population size lies in `[lower, upper]` and each earlier positive-age size
  lies in `(0, upper)`. `growthTrialSuccess_measurable` places this event in the
  generation-`duration` domain filtration. Under binary reproduction and
  nonempty selected families, `growthTrialSuccess_of_population_ge_lower`
  derives this event from `lower ≤ (StepSelection.population R duration ω).card`
  and `2 ^ duration ≤ upper`.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A split is a step at which the chosen finite offspring rule retains at
least two children. -/
def splitBy {α X : Type*} (R : Step.FiniteSelection α X) : Set (Step α X) :=
  {ξ | 2 ≤ (R ξ).card}

theorem splitBy_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] (R : Step.FiniteSelection α X)
    (hR : Measurable R.select) : MeasurableSet (splitBy R) := by
  change MeasurableSet {ξ | 2 ≤ (R ξ).card}
  have hcard : Measurable (fun ξ : Step α X => (R ξ).card) :=
    (measurable_of_countable fun s : Finset α => s.card).comp hR
  exact hcard measurableSet_Ici

/-- The event for a finite growth trial. The endpoint has population in
`[lower, upper]`; at every earlier positive age the process is nonempty and
has population strictly below `upper`. -/
def growthTrialSuccess {α X : Type*} (R : Step.FiniteSelection α X)
    (lower upper duration : ℕ) (ω : Mark α (Step α X)) : Prop :=
    lower ≤ (StepSelection.population R duration ω).card ∧
    (StepSelection.population R duration ω).card ≤ upper ∧
    ∀ k : Fin (duration - 1),
      0 < (StepSelection.population R (k.val + 1) ω).card ∧
        (StepSelection.population R (k.val + 1) ω).card < upper

theorem growthTrialSuccess_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] (R : Step.FiniteSelection α X)
    (hR : Measurable R.select) (lower upper duration : ℕ) :
    MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | growthTrialSuccess R lower upper duration ω} := by
  have hcard (k : ℕ) : Measurable[generationFiltration (M := Step α X) k]
      (fun ω => (StepSelection.population R k ω).card) := by
    exact (measurable_of_countable fun s : Finset (TreeNode α) => s.card).comp
      (StepSelection.population_adapted R hR k)
  have hend := hcard duration
  have hendlo : MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | lower ≤ (StepSelection.population R duration ω).card} :=
    hend measurableSet_Ici
  have hendhi : MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | (StepSelection.population R duration ω).card ≤ upper} :=
    hend measurableSet_Iic
  have hinterEq :
      {ω | ∀ k : Fin (duration - 1),
        0 < (StepSelection.population R (k.val + 1) ω).card ∧
          (StepSelection.population R (k.val + 1) ω).card < upper} =
        ⋂ k : Fin (duration - 1),
          {ω | 0 < (StepSelection.population R (k.val + 1) ω).card ∧
            (StepSelection.population R (k.val + 1) ω).card < upper} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  have hinter : MeasurableSet[generationFiltration (M := Step α X) duration]
      {ω | ∀ k : Fin (duration - 1),
        0 < (StepSelection.population R (k.val + 1) ω).card ∧
          (StepSelection.population R (k.val + 1) ω).card < upper} := by
    rw [hinterEq]
    apply MeasurableSet.iInter
    intro k
    have hlocal := hcard (k.val + 1)
    have hle : k.val + 1 ≤ duration := by omega
    have hglobal : Measurable[generationFiltration (M := Step α X) duration]
        (fun ω => (StepSelection.population R (k.val + 1) ω).card) :=
      hlocal.mono (generationFiltration (M := Step α X) |>.mono hle) le_rfl
    have hpos : MeasurableSet[generationFiltration (M := Step α X) duration]
        {ω | 0 < (StepSelection.population R (k.val + 1) ω).card} :=
      hglobal measurableSet_Ioi
    have hcap : MeasurableSet[generationFiltration (M := Step α X) duration]
        {ω | (StepSelection.population R (k.val + 1) ω).card < upper} :=
      hglobal measurableSet_Iio
    exact hpos.inter hcap
  exact hendlo.inter (hendhi.inter hinter)

/-- If every one-step selected family is nonempty and reproduction is binary,
then an endpoint lower bound makes the entire finite growth trial successful.
-/
theorem growthTrialSuccess_of_population_ge_lower
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hcapacity : ∀ ξ, (S ξ).card ≤ 2)
    (ω : Mark α (Step α X))
    (hmarks : ∀ u : TreeNode α, (S (ω u)).Nonempty)
    (lower duration upper : ℕ) (hupper : 2 ^ duration ≤ upper)
    (hlower : lower ≤ (StepSelection.population S duration ω).card) :
    growthTrialSuccess S lower upper duration ω := by
  classical
  have hpop : ∀ n, (StepSelection.population S n ω).Nonempty :=
    StepSelection.population_nonempty_of_all_selected_marks_nonempty S ω hmarks
  have hcardBound : ∀ n, (StepSelection.population S n ω).card ≤ 2 ^ n := by
    intro n
    exact StepSelection.population_card_le S 2 hcapacity ω n
  have hendpointUpper :
      (StepSelection.population S duration ω).card ≤ upper :=
    (hcardBound duration).trans hupper
  refine ⟨hlower, hendpointUpper, ?_⟩
  intro k
  have hage : k.val + 1 < duration := by omega
  have hpow : 2 ^ (k.val + 1) < 2 ^ duration :=
    Nat.pow_lt_pow_right (by decide) hage
  have hsmall :
      (StepSelection.population S (k.val + 1) ω).card < upper := by
    exact (hcardBound (k.val + 1)).trans_lt (hpow.trans_le hupper)
  exact ⟨Finset.card_pos.mpr (hpop (k.val + 1)), hsmall⟩


end ProbabilityTheory.BranchingRandomWalk
