/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Ordering.ByPotential
public import Combinatorics.BranchingWalk.Step.Measurability
public import Probability.BranchingProcess.Offspring.FieldLaw
public import Probability.BranchingRandomWalk.Step.Ordering.Law

/-!
# Potential-ordered support of the i.i.d. step field

A raw child law is pushed through its deterministic measurable ordering.
Every address of the resulting pre-sampled field is then ordered by the law's
real potential simultaneously almost surely.

Under an ordered one-step law with nonempty support, almost every sampled
field has the least slot present at every address:

\[\mathbb P_{\mathrm{field}}\!\left(\forall u\in\mathbb V,\;
  \operatorname{survive}(\omega(u),0)\right)=1.\]

## Public declarations

* `offspringFieldLaw_all_orderedBy` states that under the ordered offspring law,
  almost every field has every node's children ordered by the law's
  potential. `offspringFieldLaw_all_nonempty` lifts full nonempty support of the
  one-step law to every node of almost every field; `offspringFieldLaw_nonempty_at`
  is its fixed-node form.
* `offspringFieldLaw_all_first_child` combines orderedness and nonempty support to
  show that, almost surely, the least slot survives at every node.
-/

@[expose] public section

open MeasureTheory
namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)
open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

section Generic
variable {α X : Type*}

private lemma offspringFieldLaw_mem_at_of_measure_eq_one
    [MeasurableSpace X]
    (A : Set (Combinatorics.Branching.Step α X)) (hA : MeasurableSet A)
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ A = 1) (u : TreeNode α) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ω u ∈ A := by
  have hpre : offspringFieldLaw μ
      {ω : Combinatorics.Branching.StepField α X | ω u ∈ A} = μ A := by
    calc
      offspringFieldLaw μ {ω : Combinatorics.Branching.StepField α X | ω u ∈ A} =
          ((offspringFieldLaw μ).map fun ω => ω u) A := by
        rw [Measure.map_apply (measurable_pi_apply u) hA]
        rfl
      _ = μ A := by rw [offspringFieldLaw_coordinate]
  apply (ae_mem_iff_measure_eq
    ((measurable_pi_apply u) hA).nullMeasurableSet).2
  change offspringFieldLaw μ {ω | ω u ∈ A} = (offspringFieldLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem offspringFieldLaw_all_orderedBy
    {ι : Type*} [Countable α] [MeasurableSpace X] [LT α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw] :
    ∀ᵐ ω ∂offspringFieldLaw L.sorted, ∀ u : TreeNode α,
      (ω u).IsOrderedBy L.potential := by
  have hmeas := orderedBySteps_measurable (ι := α) L.potential
  have hsorted : L.sorted (orderedBySteps L.potential) = 1 := by
    rw [show orderedBySteps L.potential =
      {ξ | ξ.IsOrderedBy L.potential} from rfl,
      L.sorted_orderedBy hmeas]
    simp
  exact ae_all_iff.2
    (offspringFieldLaw_mem_at_of_measure_eq_one _ hmeas L.sorted hsorted)

theorem offspringFieldLaw_nonempty_at [Countable α] [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1)
    (u : TreeNode α) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ω u ∈ nonemptySupport :=
  offspringFieldLaw_mem_at_of_measure_eq_one nonemptySupport
    nonemptySupport_measurable μ hμ u

theorem offspringFieldLaw_all_nonempty [Countable α] [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂offspringFieldLaw μ, ∀ u : TreeNode α, ω u ∈ nonemptySupport :=
  ae_all_iff.2 (offspringFieldLaw_nonempty_at μ hμ)

/-- Potential ordering and nonemptiness force the least slot to survive. -/
theorem offspringFieldLaw_all_first_child
    {ι : Type*} [Countable α] [PartialOrder α] [OrderBot α]
    [MeasurableSpace X]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1) :
    ∀ᵐ ω ∂offspringFieldLaw L.sorted, ∀ u : TreeNode α,
      survive (ω u) ⊥ := by
  have hsortedNonempty : L.sorted nonemptySupport = 1 := by
    rw [L.sorted_nonemptySupport, hnonempty]
  filter_upwards [offspringFieldLaw_all_orderedBy L,
    offspringFieldLaw_all_nonempty L.sorted hsortedNonempty] with ω hord hne
  intro u
  obtain ⟨i, hi⟩ := hne u
  have himap : survive ((ω u).map L.potential) i :=
    (survive_map_iff L.potential _ _).2 hi
  have hbotmap : survive ((ω u).map L.potential) ⊥ :=
    orderedSteps_survive_of_le _ (hord u) bot_le himap
  exact (survive_map_iff L.potential _ _).1 hbotmap

end Generic
end ProbabilityTheory.BranchingRandomWalk
