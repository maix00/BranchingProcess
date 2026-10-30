/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Markov.Basic
public import Probability.Process.Markov.Stopping.Basic

/-!
# Strong Markov property of the canonical random walk

## Public declarations

`iidSequenceLaw_isStrongMarkovChain` states that the position process
$X_n=x+\sum_{j<n}\xi_j$ under the IID sequence law is strong Markov at every
natural-valued stopping time $T$ for its prefix domain flow. For every
duration $k\in\mathbb N$ and measurable set $A$, the stopping-time
$\sigma$-algebra identity is
\[
  \mathbb E\!\left[\mathbf 1_{\{X_{T+k}\in A\}}\mid\mathcal F_T\right]
    =(Q_\nu^{\,k})(X_T,A)\quad\text{almost surely}.
\]
For $k=1$, this right-hand side is
$\int \mathbf 1_A(X_T+z)\,\nu(dz)$. The theorem obtains the full family of
identities from the general discrete-time Markov-chain result.
-/

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilityTheory.RandomWalk


variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E] [StandardBorelSpace E]

/-- The canonical IID additive walk is strong Markov at every
natural-number-valued stopping time. -/
theorem iidSequenceLaw_isStrongMarkovChain
    (nu : Measure E) [IsProbabilityMeasure nu] (initial : E) :
    IsStrongMarkovChain (positionProcess initial)
      (sequencePrefixFiltration (E := E)) (iidSequenceLaw nu)
      (incrementKernel nu) :=
  (iidSequenceLaw_isMarkovChain nu initial).isStrongMarkovChain

end ProbabilityTheory.RandomWalk
