/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.Branching.Basic
public import Probability.BranchingProcess.Offspring.FieldLaw

/-!
# Presampled Galton--Watson branching configurations

This probability law samples one offspring configuration independently at
every potential Ulam--Harris address and retains the complete sampled field.
The realized genealogy and its generation sizes are observations of that
presampled configuration.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

open MeasureTheory

/-- The law of a presampled unmarked branching configuration obtained by
independently sampling the offspring law at every potential address. -/
noncomputable def law {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1}) :
    ProbabilityMeasure (Combinatorics.Branching.Process ι) :=
  μ.fieldLaw.map Combinatorics.Branching.branchingOfStepField

/-- Reading the complete offspring field from the presampled law recovers its
independent configuration-field law. -/
theorem law_stepField {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1}) :
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

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
