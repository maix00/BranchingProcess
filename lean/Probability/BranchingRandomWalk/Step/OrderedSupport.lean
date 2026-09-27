import Combinatorics.BranchingWalk.Step.Monotone
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Step.Law
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Ordered support of the i.i.d. step field

If one child law is supported on ordered steps, then every address of the pre-sampled tree carries an ordered
step simultaneously almost surely. The statements are generic in the slot type and in the mark type, exactly
as in `Combinatorics/BranchingWalk/`: what the mark comparison costs is the measurability of `orderedSteps`,
which is a hypothesis here and is discharged for real marks at the end of the file. The paper's model is the case
`α = ℕ`, `X = ℝ`.

This is a transfer lemma only: the enumeration of an abstract point-process law by ordered marks still needs
proof.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

section Generic

variable {α X : Type*}

theorem stepFieldLaw_ordered_at [MeasurableSpace X] [LT α] [LE X]
    (hmeas : MeasurableSet (orderedSteps : Set (Step α X)))
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (hμ : μ orderedSteps = 1)
    (u : TreeNode α) :
    ∀ᵐ ω ∂stepFieldLaw μ, ω u ∈ orderedSteps := by
  have hpre : stepFieldLaw μ {ω : StepField α X | ω u ∈ orderedSteps} = μ orderedSteps := by
    calc
      stepFieldLaw μ {ω : StepField α X | ω u ∈ orderedSteps} =
          ((stepFieldLaw μ).map fun ω => ω u) orderedSteps := by
        rw [Measure.map_apply (measurable_pi_apply u) hmeas]
        rfl
      _ = μ orderedSteps := by rw [stepFieldLaw_coordinate]
  change ∀ᵐ ω ∂stepFieldLaw μ, ω ∈ (fun ω : StepField α X => ω u) ⁻¹' orderedSteps
  apply (ae_mem_iff_measure_eq ((measurable_pi_apply u) hmeas).nullMeasurableSet).2
  change stepFieldLaw μ {ω : StepField α X | ω u ∈ orderedSteps} = (stepFieldLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem stepFieldLaw_all_ordered [Countable α] [MeasurableSpace X] [LT α] [LE X]
    (hmeas : MeasurableSet (orderedSteps : Set (Step α X)))
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (hμ : μ orderedSteps = 1) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : TreeNode α, ω u ∈ orderedSteps :=
  ae_all_iff.2 (stepFieldLaw_ordered_at hmeas μ hμ)

theorem stepFieldLaw_nonempty_at [Countable α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1)
    (u : TreeNode α) :
    ∀ᵐ ω ∂stepFieldLaw μ, ω u ∈ nonemptySupport := by
  have hpre : stepFieldLaw μ {ω : StepField α X | ω u ∈ nonemptySupport} = μ nonemptySupport := by
    calc
      stepFieldLaw μ {ω : StepField α X | ω u ∈ nonemptySupport} =
          ((stepFieldLaw μ).map fun ω => ω u) nonemptySupport := by
        rw [Measure.map_apply (measurable_pi_apply u) nonemptySupport_measurable]
        rfl
      _ = μ nonemptySupport := by rw [stepFieldLaw_coordinate]
  have hset : MeasurableSet {ω : StepField α X | ω u ∈ nonemptySupport} :=
    (measurable_pi_apply u) nonemptySupport_measurable
  apply (ae_mem_iff_measure_eq hset.nullMeasurableSet).2
  rw [hpre, hμ]
  simp

theorem stepFieldLaw_all_nonempty [Countable α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : TreeNode α, ω u ∈ nonemptySupport :=
  ae_all_iff.2 (stepFieldLaw_nonempty_at μ hμ)

/-- Under ordered support and the assumption that a child exists, the first slot of every address survives
almost surely. The first slot is `⊥`, which is `0` for the paper's slot type `ℕ`. -/
theorem stepFieldLaw_all_first_child [Countable α] [PartialOrder α] [OrderBot α]
    [MeasurableSpace X] [LE X]
    (hmeas : MeasurableSet (orderedSteps : Set (Step α X)))
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (hordered : μ orderedSteps = 1) (hnonempty : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : TreeNode α, survive (ω u) ⊥ := by
  filter_upwards [stepFieldLaw_all_ordered hmeas μ hordered,
    stepFieldLaw_all_nonempty μ hnonempty] with ω hord hne
  intro u
  obtain ⟨i, hi⟩ := hne u
  exact orderedSteps_survive_of_le (ω u) (hord u) bot_le hi

end Generic

section NatReal

/-- The paper's case: `ℕ` slots and real marks, where the comparison graph is measurable. -/
theorem stepFieldLaw_all_ordered_natReal (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (hμ : μ orderedSteps = 1) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : 𝕍, ω u ∈ orderedSteps :=
  stepFieldLaw_all_ordered (orderedSteps_measurable (ι := ℕ)) μ hμ

/-- The paper's case: with ordered support and at least one child, slot zero survives at every node almost
surely. -/
theorem stepFieldLaw_all_first_child_natReal (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (hordered : μ orderedSteps = 1) (hnonempty : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂stepFieldLaw μ, ∀ u : 𝕍, survive (ω u) 0 :=
  stepFieldLaw_all_first_child (orderedSteps_measurable (ι := ℕ)) μ hordered hnonempty

end NatReal

end ProbabilityTheory.BranchingRandomWalk
