import Combinatorics.BranchingWalk.Step.Monotone
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Step.Law
import Probability.BranchingRandomWalk.Step.OrderingLaw
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Ordered support of the i.i.d. step field

A raw child law is first pushed through its deterministic measurable ordering.
Every address of the resulting i.i.d. pre-sampled tree then carries an ordered
step simultaneously almost surely. Ordered support is a theorem about this
derived law, never an assumption on the raw law.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

section Generic

variable {α X : Type*}

private theorem stepFieldLaw_ordered_at_of_measure_eq_one
    [MeasurableSpace X] [LT α] [LE X]
    (hmeas : MeasurableSet (orderedSteps : Set (Combinatorics.Branching.Step α X)))
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ orderedSteps = 1)
    (u : TreeNode α) :
    ∀ᵐ ω ∂stepFieldLaw μ, ω u ∈ orderedSteps := by
  have hpre : stepFieldLaw μ
      {ω : Combinatorics.Branching.StepField α X | ω u ∈ orderedSteps} =
      μ orderedSteps := by
    calc
      stepFieldLaw μ {ω : Combinatorics.Branching.StepField α X |
          ω u ∈ orderedSteps} =
          ((stepFieldLaw μ).map fun ω => ω u) orderedSteps := by
        rw [Measure.map_apply (measurable_pi_apply u) hmeas]
        rfl
      _ = μ orderedSteps := by rw [stepFieldLaw_coordinate]
  change ∀ᵐ ω ∂stepFieldLaw μ, ω ∈
    (fun ω : Combinatorics.Branching.StepField α X => ω u) ⁻¹' orderedSteps
  apply (ae_mem_iff_measure_eq ((measurable_pi_apply u) hmeas).nullMeasurableSet).2
  change stepFieldLaw μ
    {ω : Combinatorics.Branching.StepField α X | ω u ∈ orderedSteps} =
      (stepFieldLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem stepFieldLaw_all_ordered
    {ι : Type*} [Countable α] [MeasurableSpace X] [LT α] [LE X]
    (hmeas : MeasurableSet
      (orderedSteps : Set (Combinatorics.Branching.Step α X)))
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw] :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : TreeNode α,
      ω u ∈ orderedSteps := by
  have hsorted : L.sorted orderedSteps = 1 := by
    rw [L.sorted_ordered hmeas]
    simp
  exact ae_all_iff.2
    (stepFieldLaw_ordered_at_of_measure_eq_one hmeas L.sorted hsorted)

theorem stepFieldLaw_nonempty_at [Countable α] [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1)
    (u : TreeNode α) :
    ∀ᵐ ω ∂stepFieldLaw μ, ω u ∈ nonemptySupport := by
  have hpre : stepFieldLaw μ
      {ω : Combinatorics.Branching.StepField α X |
        ω u ∈ nonemptySupport} = μ nonemptySupport := by
    calc
      stepFieldLaw μ {ω : Combinatorics.Branching.StepField α X |
          ω u ∈ nonemptySupport} =
          ((stepFieldLaw μ).map fun ω => ω u) nonemptySupport := by
        rw [Measure.map_apply (measurable_pi_apply u) nonemptySupport_measurable]
        rfl
      _ = μ nonemptySupport := by rw [stepFieldLaw_coordinate]
  have hset : MeasurableSet
      {ω : Combinatorics.Branching.StepField α X |
        ω u ∈ nonemptySupport} :=
    (measurable_pi_apply u) nonemptySupport_measurable
  apply (ae_mem_iff_measure_eq hset.nullMeasurableSet).2
  rw [hpre, hμ]
  simp

theorem stepFieldLaw_all_nonempty [Countable α] [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : TreeNode α, ω u ∈ nonemptySupport :=
  ae_all_iff.2 (stepFieldLaw_nonempty_at μ hμ)

/-- Under ordered support and the assumption that a child exists, the first slot of every address survives
almost surely. The first slot is `⊥`, which is `0` for the paper's slot type `ℕ`. -/
theorem stepFieldLaw_all_first_child
    {ι : Type*} [Countable α] [PartialOrder α] [OrderBot α]
    [MeasurableSpace X] [LE X]
    (hmeas : MeasurableSet
      (orderedSteps : Set (Combinatorics.Branching.Step α X)))
    (L : StepLaw ι α X) [Zero X] [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : TreeNode α,
      survive (ω u) ⊥ := by
  have hsortedNonempty : L.sorted nonemptySupport = 1 := by
    rw [L.sorted_nonemptySupport, hnonempty]
  filter_upwards [stepFieldLaw_all_ordered hmeas L,
    stepFieldLaw_all_nonempty L.sorted hsortedNonempty] with ω hord hne
  intro u
  obtain ⟨i, hi⟩ := hne u
  exact orderedSteps_survive_of_le (ω u) (hord u) bot_le hi

end Generic

section NatReal

/-- The paper's case: `ℕ` slots and real marks, where the comparison graph is measurable. -/
theorem stepFieldLaw_all_ordered_natReal {ι : Type*}
    (L : StepLaw ι ℕ ℝ) [IsProbabilityMeasure L.raw] :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : 𝕍, ω u ∈ orderedSteps :=
  stepFieldLaw_all_ordered (orderedSteps_measurable (ι := ℕ)) L

/-- The paper's case: with ordered support and at least one child, slot zero survives at every node almost
surely. -/
theorem stepFieldLaw_all_first_child_natReal {ι : Type*}
    (L : StepLaw ι ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnonempty : L.raw nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw L.sorted, ∀ u : 𝕍, survive (ω u) 0 :=
  stepFieldLaw_all_first_child (orderedSteps_measurable (ι := ℕ)) L hnonempty

end NatReal

end ProbabilityTheory.BranchingRandomWalk
