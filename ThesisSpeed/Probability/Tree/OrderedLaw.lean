import ThesisSpeed.Probability.Tree.OrderedOffspring
import ThesisSpeed.Probability.Tree.OffspringLaw

/-!
# Ordered support of the i.i.d. marked tree

If a single offspring law is supported on ordered marks, then every address
of the pre-sampled countable tree has an ordered mark simultaneously almost
surely. This is a transfer lemma only: the representation of an abstract
point-process law by ordered marks still needs proof.
-/

open MeasureTheory

namespace ThesisSpeed

theorem iidMarkedTree_ordered_at (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (hμ : μ orderedOffspring = 1)
    (u : TreeNode) :
    ∀ᵐ ω ∂iidMarkedTreeLaw μ, ω u ∈ orderedOffspring := by
  have hpre : iidMarkedTreeLaw μ
      {ω : MarkedTree OffspringMark | ω u ∈ orderedOffspring} =
      μ orderedOffspring := by
    calc
      iidMarkedTreeLaw μ {ω : MarkedTree OffspringMark |
          ω u ∈ orderedOffspring} =
          ((iidMarkedTreeLaw μ).map (fun ω => ω u)) orderedOffspring := by
            rw [Measure.map_apply (measurable_pi_apply u)
              orderedOffspring_measurable]
            rfl
      _ = μ orderedOffspring := by rw [iidMarkedTree_marginal]
  apply (ae_mem_iff_measure_eq
    ((measurable_pi_apply u) orderedOffspring_measurable).nullMeasurableSet).2
  change iidMarkedTreeLaw μ
    {ω : MarkedTree OffspringMark | ω u ∈ orderedOffspring} =
      (iidMarkedTreeLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem iidMarkedTree_all_ordered (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (hμ : μ orderedOffspring = 1) :
    ∀ᵐ ω ∂iidMarkedTreeLaw μ, ∀ u : TreeNode,
      ω u ∈ orderedOffspring := by
  exact ae_all_iff.2 (iidMarkedTree_ordered_at μ hμ)

end ThesisSpeed
