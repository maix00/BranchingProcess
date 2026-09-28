import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Topology.ContinuousMap.Compactness

/-!
# Tight families of continuous-path laws

This file turns deterministic Arzelà--Ascoli bounds into tightness of a
family of measures on continuous path space.  The statement is independent
of any increment law or stochastic-process model.
-/

open MeasureTheory Set

namespace ProbabilityTheory.Process.Path

/-- A family of continuous-path measures is tight if, outside arbitrarily
small mass, its paths belong to one equicontinuous family with a common
pointwise bound. -/
theorem isTightMeasureSet_of_equicontinuous_bounded
    {I T E : Type*} [TopologicalSpace T] [CompactlyCoherentSpace T]
    [MetricSpace E] [ProperSpace E]
    (mu : I → Measure C(T, E))
    (h : ∀ epsilon, 0 < epsilon →
      ∃ S : Set C(T, E),
        Equicontinuous ((↑) : S → T → E) ∧
        ∃ origin : E, ∃ radius : ℝ,
          (∀ f ∈ S, ∀ t, dist (f t) origin ≤ radius) ∧
          ∀ i, mu i Sᶜ ≤ epsilon) :
    IsTightMeasureSet (range mu) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  obtain ⟨S, hS, origin, radius, hbound, hmass⟩ := h epsilon hepsilon
  refine ⟨closure S,
    ContinuousMap.isCompact_closure_of_equicontinuous_of_bounded
      S hS origin radius hbound, ?_⟩
  intro nu hnu
  obtain ⟨i, rfl⟩ := hnu
  exact (measure_mono (compl_subset_compl.mpr subset_closure)).trans (hmass i)

end ProbabilityTheory.Process.Path
