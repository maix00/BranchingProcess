/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Markov
public import Probability.Process.Markov.Stopping.Basic

/-!
# Strong Markov property of the canonical random walk

The canonical IID additive walk inherits the finite-stopping-time strong
Markov property from the general discrete Markov-chain theorem.
-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E] [StandardBorelSpace E] [Nonempty E]

/-- The canonical IID additive walk is strong Markov at every
natural-number-valued stopping time. -/
theorem iidSequenceLaw_isStrongMarkovChain
    (nu : Measure E) [IsProbabilityMeasure nu] (initial : E) :
    IsStrongMarkovChain (positionProcess initial)
      (incrementFiltration (E := E)) (iidSequenceLaw nu)
      (incrementKernel nu) :=
  (iidSequenceLaw_isMarkovChain nu initial).isStrongMarkovChain

end ProbabilityTheory.RandomWalk
