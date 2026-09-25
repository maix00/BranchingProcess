import ThesisSpeed.Probability.PointProcess.Enumeration.Order
import ThesisSpeed.Probability.PointProcess.Law.IID

/-!
# Ordered support of the i.i.d. marked tree

If a single offspring law is supported on ordered marks, then every address
of the pre-sampled countable tree has an ordered mark simultaneously almost
surely. This is a transfer lemma only: the representation of an abstract
point-process law by ordered marks still needs proof.
-/

open MeasureTheory

namespace ThesisSpeed

theorem iidMark_ordered_at (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ orderedOffspring = 1)
    (u : 𝕍) :
    ∀ᵐ ω ∂iidMarkLaw μ, ω u ∈ orderedOffspring := by
  have hpre : iidMarkLaw μ
      {ω : Mark ℕ WeightedBranchingStep | ω u ∈ orderedOffspring} =
      μ orderedOffspring := by
    calc
      iidMarkLaw μ {ω : Mark ℕ WeightedBranchingStep |
          ω u ∈ orderedOffspring} =
          ((iidMarkLaw μ).map (fun ω => ω u)) orderedOffspring := by
            rw [Measure.map_apply (measurable_pi_apply u)
              orderedOffspring_measurable]
            rfl
      _ = μ orderedOffspring := by rw [iidMark_marginal]
  apply (ae_mem_iff_measure_eq
    ((measurable_pi_apply u) orderedOffspring_measurable).nullMeasurableSet).2
  change iidMarkLaw μ
    {ω : Mark ℕ WeightedBranchingStep | ω u ∈ orderedOffspring} =
      (iidMarkLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem iidMark_all_ordered (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ orderedOffspring = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ orderedOffspring := by
  exact ae_all_iff.2 (iidMark_ordered_at μ hμ)

theorem iidMark_nonempty_at (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ offspringNonempty = 1)
    (u : 𝕍) :
    ∀ᵐ ω ∂iidMarkLaw μ, ω u ∈ offspringNonempty := by
  have hpre : iidMarkLaw μ
      {ω : Mark ℕ WeightedBranchingStep | ω u ∈ offspringNonempty} =
      μ offspringNonempty := by
    calc
      iidMarkLaw μ {ω : Mark ℕ WeightedBranchingStep |
          ω u ∈ offspringNonempty} =
          ((iidMarkLaw μ).map (fun ω => ω u)) offspringNonempty := by
            rw [Measure.map_apply (measurable_pi_apply u)
              offspringNonempty_measurable]
            rfl
      _ = μ offspringNonempty := by rw [iidMark_marginal]
  have hset : MeasurableSet
      {ω : Mark ℕ WeightedBranchingStep | ω u ∈ offspringNonempty} :=
    (measurable_pi_apply u) offspringNonempty_measurable
  apply (ae_mem_iff_measure_eq hset.nullMeasurableSet).2
  rw [hpre, hμ]
  simp

theorem iidMark_all_nonempty (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ offspringNonempty = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ offspringNonempty := by
  exact ae_all_iff.2 (iidMark_nonempty_at μ hμ)

/-- Under ordered support and the thesis's at-least-one-child assumption,
slot zero is present at every node almost surely. -/
theorem iidMark_all_first_child (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ]
    (hordered : μ orderedOffspring = 1)
    (hnonempty : μ offspringNonempty = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ childRealized 0 := by
  filter_upwards [iidMark_all_ordered μ hordered,
    iidMark_all_nonempty μ hnonempty] with ω hord hne
  intro u
  obtain ⟨i, hi⟩ := hne u
  exact orderedOffspring_first_present (ω u) (hord u) i hi

end ThesisSpeed
