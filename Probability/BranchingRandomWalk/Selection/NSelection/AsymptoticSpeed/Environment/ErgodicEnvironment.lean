/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Probability.Ergodic.IIDShift

/-!
# Ergodicity of the generation environment

This module specializes the general i.i.d.-sequence shift theorem to the
pre-sampled generation environment. The general proof identifies invariant
events with tail events and applies Kolmogorov's zero-one law.

## Public declarations

For the product environment law $\mathbb P_N$ and one-sided shift
$(\theta\omega)_k=\omega_{k+1}$ defined in `Environment.Basic`, the public
theorem states $\operatorname{Ergodic}(\theta,\mathbb P_N)$.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- The shift of the i.i.d. generation environment is ergodic. -/
theorem generationEnvironmentShift_ergodic
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    Ergodic (generationEnvironmentShift : GenerationEnvironment N →
      GenerationEnvironment N) (generationEnvironmentLaw μ N) := by
  change Ergodic (fun ω : ℕ → GenerationBatch N => fun n => ω (n + 1)) _
  simpa [generationEnvironmentLaw] using
    (ProbabilityTheory.iidSequenceShift_ergodic
      (μ := generationBatchLaw μ N))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
