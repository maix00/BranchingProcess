import Probability.BranchingRandomWalk.Step.Law

/-!
# Independence on a pre-sampled tree

The address map is supplied as ordinary deterministic data.  In particular,
the theorem below does not require the selected addresses to be stopping
times.  This is the formal interface used for reserve branches and stopping
line arguments: once the addresses are fixed on the pre-sampled tree, an
injective address map gives independent marks.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

theorem preSampled_coordinates_independent
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (σ : ι → 𝕍) (hσ : Function.Injective σ) :
    iIndepFun (fun i (ω : Mark ℕ (Step ℕ ℝ)) => ω (σ i))
      (stepFieldLaw μ) :=
  stepFieldLaw_injective_coordinates_independent μ σ hσ

theorem preSampled_displacements_independent
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (σ : ι → 𝕍) (hσ : Function.Injective σ) :
    iIndepFun
      (fun i (ω : Mark ℕ (Step ℕ ℝ)) => value' (ω (σ i)) 0)
      (stepFieldLaw μ) :=
  stepFieldLaw_injective_displacements_independent μ σ hσ

theorem preSampled_measurable_observables_independent
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (σ : ι → 𝕍) (hσ : Function.Injective σ)
    (g : ∀ i, Step ℕ ℝ → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun
      (fun i (ω : Mark ℕ (Step ℕ ℝ)) => g i (ω (σ i)))
      (stepFieldLaw μ) :=
  stepFieldLaw_injective_coordinates_comp_independent μ σ hσ g hg

end ProbabilityTheory.BranchingRandomWalk
