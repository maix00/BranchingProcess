module

public import Combinatorics.BranchingWalk.Step.Potential
public import Combinatorics.BranchingWalk.Step.Measurability
public import Probability.BranchingRandomWalk.Step.Law
public import Probability.BranchingRandomWalk.Step.OrderingLaw

@[expose] public section

/-!
# Potential-ordered support of the i.i.d. step field

A raw child law is pushed through its deterministic measurable ordering.
Every address of the resulting pre-sampled field is then ordered by the law's
real potential simultaneously almost surely.
-/

open MeasureTheory
namespace ProbabilityTheory.BranchingRandomWalk
open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

section Generic
variable {α X : Type*}

private theorem stepFieldLaw_mem_at_of_measure_eq_one
    [MeasurableSpace X]
    (A : Set (Combinatorics.Branching.Step α X)) (hA : MeasurableSet A)
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ A = 1) (u : TreeNode α) :
    ∀ᵐ ω ∂stepFieldLaw μ, ω u ∈ A := by
  have hpre : stepFieldLaw μ
      {ω : Combinatorics.Branching.StepField α X | ω u ∈ A} = μ A := by
    calc
      stepFieldLaw μ {ω : Combinatorics.Branching.StepField α X | ω u ∈ A} =
          ((stepFieldLaw μ).map fun ω => ω u) A := by
        rw [Measure.map_apply (measurable_pi_apply u) hA]
        rfl
      _ = μ A := by rw [stepFieldLaw_coordinate]
  apply (ae_mem_iff_measure_eq
    ((measurable_pi_apply u) hA).nullMeasurableSet).2
  change stepFieldLaw μ {ω | ω u ∈ A} = (stepFieldLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem stepFieldLaw_all_orderedBy
    {ι : Type*} [Countable α] [MeasurableSpace X] [LT α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw] :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : TreeNode α,
      (ω u).IsOrderedBy L.potential := by
  have hmeas := orderedBySteps_measurable (ι := α) L.potential
  have hsorted : L.sorted (orderedBySteps L.potential) = 1 := by
    rw [show orderedBySteps L.potential =
      {ξ | ξ.IsOrderedBy L.potential} from rfl,
      L.sorted_orderedBy hmeas]
    simp
  exact ae_all_iff.2
    (stepFieldLaw_mem_at_of_measure_eq_one _ hmeas L.sorted hsorted)

theorem stepFieldLaw_nonempty_at [Countable α] [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1)
    (u : TreeNode α) :
    ∀ᵐ ω ∂stepFieldLaw μ, ω u ∈ nonemptySupport :=
  stepFieldLaw_mem_at_of_measure_eq_one nonemptySupport
    nonemptySupport_measurable μ hμ u

theorem stepFieldLaw_all_nonempty [Countable α] [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : TreeNode α, ω u ∈ nonemptySupport :=
  ae_all_iff.2 (stepFieldLaw_nonempty_at μ hμ)

/-- Potential ordering and nonemptiness force the least slot to survive. -/
theorem stepFieldLaw_all_first_child
    {ι : Type*} [Countable α] [PartialOrder α] [OrderBot α]
    [MeasurableSpace X]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : TreeNode α,
      survive (ω u) ⊥ := by
  have hsortedNonempty : L.sorted nonemptySupport = 1 := by
    rw [L.sorted_nonemptySupport, hnonempty]
  filter_upwards [stepFieldLaw_all_orderedBy L,
    stepFieldLaw_all_nonempty L.sorted hsortedNonempty] with ω hord hne
  intro u
  obtain ⟨i, hi⟩ := hne u
  have himap : survive ((ω u).map L.potential) i :=
    (survive_map_iff L.potential _ _).2 hi
  have hbotmap : survive ((ω u).map L.potential) ⊥ :=
    orderedSteps_survive_of_le _ (hord u) bot_le himap
  exact (survive_map_iff L.potential _ _).1 hbotmap

end Generic

section NatSlots

theorem stepFieldLaw_all_ordered_natReal {ι : Type*}
    (L : StepLaw ι ℕ ℝ) [IsProbabilityMeasure L.raw] :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : 𝕍,
      (ω u).IsOrderedBy L.potential :=
  stepFieldLaw_all_orderedBy L

theorem stepFieldLaw_all_first_child_natReal {ι : Type*}
    (L : StepLaw ι ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : 𝕍, survive (ω u) 0 :=
  stepFieldLaw_all_first_child L hnonempty

end NatSlots
end ProbabilityTheory.BranchingRandomWalk
