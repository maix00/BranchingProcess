/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.BranchingProcess.GaltonWatson.Generation

/-!
# Independence of Galton--Watson offspring configurations

The canonical tree law is the image of an i.i.d. field. This module exposes
the coordinate independence directly at the branching-process boundary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingProcess.GaltonWatson

/-- Under the Galton--Watson field law, offspring configurations at distinct
addresses are mutually independent. Dependence between siblings within one
configuration is unrestricted. -/
theorem field_independent {ι : Type*}
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit.{1}) :
    iIndepFun
      (fun u (field : Combinatorics.Branching.StepField ι PUnit.{1}) => field u)
      (μ.fieldLaw : Measure (Combinatorics.Branching.StepField ι PUnit.{1})) := by
  rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.fieldLaw_toMeasure]
  exact ProbabilityTheory.BranchingProcess.offspringFieldLaw_independent
    (α := ι) (Mark := PUnit.{1})
    (μ : Measure (Combinatorics.Branching.Step ι PUnit.{1}))

end ProbabilityTheory.BranchingProcess.GaltonWatson

end
