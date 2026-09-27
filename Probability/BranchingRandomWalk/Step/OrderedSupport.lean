import Combinatorics.BranchingWalk.Step.Monotone
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Step.DisplacementLaw
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Ordered support of the i.i.d. marked tree

If a single child law is supported on ordered marks, then every address
of the pre-sampled countable tree has an ordered mark simultaneously almost
surely. This is a transfer lemma only: the enumeration of an abstract
point-process law by ordered marks still needs proof.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



theorem iidMark_ordered_at (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (hμ : μ orderedSteps = 1)
    (u : 𝕍) :
    ∀ᵐ ω ∂iidMarkLaw μ, ω u ∈ orderedSteps := by
  have hpre : iidMarkLaw μ
      {ω : Mark ℕ (Step ℕ ℝ) | ω u ∈ orderedSteps} =
      μ orderedSteps := by
    calc
      iidMarkLaw μ {ω : Mark ℕ (Step ℕ ℝ) |
          ω u ∈ orderedSteps} =
          ((iidMarkLaw μ).map (fun ω => ω u)) orderedSteps := by
            rw [Measure.map_apply (measurable_pi_apply u)
              orderedSteps_measurable]
            rfl
      _ = μ orderedSteps := by rw [iidMark_marginal]
  change ∀ᵐ ω ∂iidMarkLaw μ,
    ω ∈ (fun ω : Mark ℕ (Step ℕ ℝ) => ω u) ⁻¹' orderedSteps
  apply (ae_mem_iff_measure_eq
    ((measurable_pi_apply u) orderedSteps_measurable).nullMeasurableSet).2
  change iidMarkLaw μ
    {ω : Mark ℕ (Step ℕ ℝ) | ω u ∈ orderedSteps} =
      (iidMarkLaw μ) Set.univ
  rw [hpre, hμ]
  simp

theorem iidMark_all_ordered (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (hμ : μ orderedSteps = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ orderedSteps := by
  exact ae_all_iff.2 (iidMark_ordered_at μ hμ)

theorem iidMark_nonempty_at (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1)
    (u : 𝕍) :
    ∀ᵐ ω ∂iidMarkLaw μ, ω u ∈ nonemptySupport := by
  have hpre : iidMarkLaw μ
      {ω : Mark ℕ (Step ℕ ℝ) | ω u ∈ nonemptySupport} =
      μ nonemptySupport := by
    calc
      iidMarkLaw μ {ω : Mark ℕ (Step ℕ ℝ) |
          ω u ∈ nonemptySupport} =
          ((iidMarkLaw μ).map (fun ω => ω u)) nonemptySupport := by
            rw [Measure.map_apply (measurable_pi_apply u)
              nonemptySupport_measurable]
            rfl
      _ = μ nonemptySupport := by rw [iidMark_marginal]
  have hset : MeasurableSet
      {ω : Mark ℕ (Step ℕ ℝ) | ω u ∈ nonemptySupport} :=
    (measurable_pi_apply u) nonemptySupport_measurable
  apply (ae_mem_iff_measure_eq hset.nullMeasurableSet).2
  rw [hpre, hμ]
  simp

theorem iidMark_all_nonempty (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (hμ : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      ω u ∈ nonemptySupport := by
  exact ae_all_iff.2 (iidMark_nonempty_at μ hμ)

/-- Under ordered support and the thesis's at-least-one-child assumption,
slot zero is survive at every node almost surely. -/
theorem iidMark_all_first_child (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (hordered : μ orderedSteps = 1)
    (hnonempty : μ nonemptySupport = 1) :
    ∀ᵐ ω ∂iidMarkLaw μ, ∀ u : 𝕍,
      survive (ω u) 0 := by
  filter_upwards [iidMark_all_ordered μ hordered,
    iidMark_all_nonempty μ hnonempty] with ω hord hne
  intro u
  obtain ⟨i, hi⟩ := hne u
  exact orderedSteps_survive_of_le (ω u) (hord u) (Nat.zero_le i) hi

end ProbabilityTheory.BranchingRandomWalk
