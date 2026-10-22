/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Probability.Process.Filtration.ConditionalBlocks
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.JumpPattern.DiscretizedMaximum
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.TubeEvent

/-!
# Jump-pattern constructions for the Lemma 3.3 proof

The internal constructions used by the proof are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownJumpPatternTubeIntersection`:
  $\bigcap_{n<q}E_{J,n}$, the intersection over all blocks.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownAdmissibleJumpPatterns`:
  $\{J\subseteq\operatorname{Fin}(q):|J|\le K\}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownJumpPatternTubeEvent`:
  $E_{J,n}=\Omega$ for $n\in J$ and the rounded-maximum tube event for
  $n<q$ with $n\notin J$; $E_{J,n}=\Omega$ for $n\ge q$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownJumpPatternBound`:
  $b_{J,n}=1$ for $n\in J$ and $b_{J,n}=p$ otherwise.

These constructions encode the discretized-maximum decomposition in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, Chapter 3, Lemma 3.3.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- For a fixed candidate jump set, impose the rounded-maximum tube on each
block outside that set and leave the jump blocks unrestricted. -/
def drawdownJumpPatternTubeEvent {q : ℕ}
    (remainder blockLength : ℕ) (pattern : Finset (Fin q))
    (upper binWidth tubeWidth : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  if hn : n < q then
    if (⟨n, hn⟩ : Fin q) ∈ pattern then Set.univ
    else drawdownTubeBlockEvent (remainder + n * blockLength) blockLength
      (drawdownPastDiscretizedMaximum
        (start := remainder + n * blockLength) upper binWidth) tubeWidth
  else Set.univ

/-- The conditional factor attached to a block for a fixed jump pattern. -/
def drawdownJumpPatternBound {q : ℕ}
    (pattern : Finset (Fin q)) (p : ℝ) (n : ℕ) : ℝ :=
  if hn : n < q then
    if (⟨n, hn⟩ : Fin q) ∈ pattern then 1 else p
  else 1

/-- The tube events selected by a fixed jump pattern, intersected over the
first `q` blocks. -/
def drawdownJumpPatternTubeIntersection {q : ℕ}
    (remainder blockLength : ℕ) (pattern : Finset (Fin q))
    (upper binWidth tubeWidth : ℝ) : Set (ℕ → ℝ) :=
  ProbabilityTheory.conditionalBlockIntersection
    (drawdownJumpPatternTubeEvent remainder blockLength pattern
      upper binWidth tubeWidth) q

/-- The finite family of jump patterns with at most `K` jump indices. -/
noncomputable def drawdownAdmissibleJumpPatterns (q K : ℕ) :
    Finset (Finset (Fin q)) :=
  Finset.univ.filter fun pattern => pattern.card ≤ K

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
