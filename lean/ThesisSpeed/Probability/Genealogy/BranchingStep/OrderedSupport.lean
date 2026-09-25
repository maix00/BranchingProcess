import ThesisSpeed.Probability.PointProcess.Slot.Order
import ThesisSpeed.Probability.Genealogy.BranchingStep.DisplacementLaw

/-!
# Ordered support of the i.i.d. marked tree

If a single child law is supported on ordered marks, then every address
of the pre-sampled countable tree has an ordered mark simultaneously almost
surely. This is a transfer lemma only: the representation of an abstract
point-process law by ordered marks still needs proof.
-/

open MeasureTheory

namespace ThesisSpeed

theorem iidMark_ordered_at (μ : Measure NatRealBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ orderedBranchingSteps = 1)
    (u : 𝕍) :
    ∀ᵐ ω ∂iidMarkLaw μ, ω u ∈ orderedBranchingSteps := by
  have hpre : iidMarkLaw μ
      {ω : Mark ℕ NatRealBranchingStep | ω u ∈ orderedBranchingSteps} =
      μ orderedBranchingSteps := by
    calc
      iidMarkLaw μ {ω : Mark ℕ NatRealBranchingStep |
          ω u ∈ orderedBranchingSteps} =
          ((iidMarkLaw μ).map (fun ω => ω u)) orderedBranchingSteps := by
            rw [Measure.map_apply (measurable_pi_apply u)
              orderedBranchingSteps_measurable]
            rfl
      _ = μ orderedBranchingSteps := by rw [iidMark_marginal]
  change ∀ᵐ ω ∂iidMarkLaw μ,
    ω ∈ (fun ω : Mark ℕ NatRealBranchingStep => ω u) ⁻¹' orderedBranchingSteps
  apply (ae_mem_iff_measure_eq
    ((measurable_pi_apply u) orderedBranchingSteps_measurable).nullMeasurableSet).2
  change iidMarkLaw μ
    {ω : Mark ℕ NatRealBranchingStep | ω u ∈ orderedBranchingSteps} =
      (iidMarkLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem iidMark_all_ordered (μ : Measure NatRealBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ orderedBranchingSteps = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ orderedBranchingSteps := by
  exact ae_all_iff.2 (iidMark_ordered_at μ hμ)

theorem iidMark_nonempty_at (μ : Measure NatRealBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ childNonempty = 1)
    (u : 𝕍) :
    ∀ᵐ ω ∂iidMarkLaw μ, ω u ∈ childNonempty := by
  have hpre : iidMarkLaw μ
      {ω : Mark ℕ NatRealBranchingStep | ω u ∈ childNonempty} =
      μ childNonempty := by
    calc
      iidMarkLaw μ {ω : Mark ℕ NatRealBranchingStep |
          ω u ∈ childNonempty} =
          ((iidMarkLaw μ).map (fun ω => ω u)) childNonempty := by
            rw [Measure.map_apply (measurable_pi_apply u)
              childNonempty_measurable]
            rfl
      _ = μ childNonempty := by rw [iidMark_marginal]
  have hset : MeasurableSet
      {ω : Mark ℕ NatRealBranchingStep | ω u ∈ childNonempty} :=
    (measurable_pi_apply u) childNonempty_measurable
  apply (ae_mem_iff_measure_eq hset.nullMeasurableSet).2
  rw [hpre, hμ]
  simp

theorem iidMark_all_nonempty (μ : Measure NatRealBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ childNonempty = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ childNonempty := by
  exact ae_all_iff.2 (iidMark_nonempty_at μ hμ)

/-- Under ordered support and the thesis's at-least-one-child assumption,
slot zero is present at every node almost surely. -/
theorem iidMark_all_first_child (μ : Measure NatRealBranchingStep)
    [IsProbabilityMeasure μ]
    (hordered : μ orderedBranchingSteps = 1)
    (hnonempty : μ childNonempty = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ childRealized 0 := by
  filter_upwards [iidMark_all_ordered μ hordered,
    iidMark_all_nonempty μ hnonempty] with ω hord hne
  intro u
  obtain ⟨i, hi⟩ := hne u
  exact orderedBranchingSteps_first_present (ω u) (hord u) i hi

end ThesisSpeed
