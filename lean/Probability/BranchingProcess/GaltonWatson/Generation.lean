module

public import Combinatorics.Branching.Basic
public import Combinatorics.BranchingWalk.Basic.GenerationSize
public import Probability.BranchingProcess.Offspring.Law

/-!
# Galton--Watson genealogy and generation size

The tree-valued Galton--Watson law starts directly from the law of one
unmarked offspring configuration. Generation sizes reuse the `ℕ∞`-valued
observation on branching walks, so infinite populations remain representable.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

open MeasureTheory

/-- The tree-valued law obtained by independently sampling the given offspring
configuration at every address. -/
noncomputable def law {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringLaw ι) :
    ProbabilityMeasure (Combinatorics.Branching.Process ι) :=
  μ.fieldLaw.map Combinatorics.Branching.branchingOfStepField

/-- Reading the complete offspring field back from the tree-valued law
recovers the original independent field law. -/
theorem law_stepField {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringLaw ι) :
    ((law μ : ProbabilityMeasure (Combinatorics.Branching.Process ι)) :
    Measure (Combinatorics.Branching.Process ι)).map
        (fun β => β.step PUnit.unit) =
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
  have hpair : Measurable
      (fun β : Combinatorics.Branching.Process ι => (β.step, β.initial)) :=
    Measurable.of_comap_le le_rfl
  have hstep : Measurable
      (fun β : Combinatorics.Branching.Process ι => β.step PUnit.unit) :=
    (measurable_pi_apply PUnit.unit).comp
      (measurable_fst.comp hpair)
  have hpack : Measurable
      (Combinatorics.Branching.branchingOfStepField (α := ι)) :=
    Combinatorics.Branching.measurable_branchingOfStepField
  rw [law, ProbabilityMeasure.toMeasure_map, Measure.map_map hstep hpack]
  have hcomp :
      (fun β : Combinatorics.Branching.Process ι => β.step PUnit.unit) ∘
          Combinatorics.Branching.branchingOfStepField = id := by
    funext field
    rfl
  rw [hcomp, Measure.map_id]

/-- The initial generation of a single-root branching process consists of its
one root particle. -/
theorem generationSize_zero {ι : Type*}
    (β : Combinatorics.Branching.Process ι) :
    β.generationSize 0 = 1 := by
  classical
  rw [Combinatorics.Branching.RootIndexed.BranchingWalk.generationSize]
  have hslice :
      Combinatorics.Branching.survivingParticlesAt β 0 =
        {(PUnit.unit, ([] : Combinatorics.UlamHarris.TreeNode ι))} := by
    ext p
    rcases p with ⟨r, u⟩
    cases r
    rw [Combinatorics.Branching.mem_survivingParticlesAt_iff,
      Combinatorics.Branching.mem_survivingParticles_iff_surviveAlong]
    simp [Combinatorics.UlamHarris.generation]
    intro hu
    subst u
    exact Combinatorics.Branching.surviveAlong_nil _ _
  rw [hslice, Set.encard_singleton]

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
