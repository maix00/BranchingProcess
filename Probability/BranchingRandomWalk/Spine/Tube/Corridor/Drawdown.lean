/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Affine
public import Probability.BranchingRandomWalk.Spine.RandomWalk.IncrementProcess

/-!
# Drawdown transfer for the tilted spine corridor

tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown
bounds the probability of a finite affine-corridor continuation under the
tilted increment field law by the corresponding generic random-walk
drawdown-and-endpoint probability. The proof applies the deterministic path
inclusion from
ProbabilityTheory.RandomWalk.affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Spine.tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown`:
  for `drift ≥ 0`, if the tilted increment law assigns probability at most
  `q` to
  `noLargeDropEndpointBelowEvent n width (width + drift * n)`, then it assigns
  probability at most `q` to the endpoint-truncated affine-corridor
  continuation obtained by prepending `x` to a length-`n` history starting
  at `x + y`.

The tilted increment law is specific to the branching spine, so this
probability transfer belongs to the branching-random-walk layer.

Writing \(S_j(z)\) for the displacement of the first \(j\) increments, the
input event is
\(\{z:\forall i\le j\le n,\ S_i(z)-S_j(z)\le\Delta,\quad
S_n(z)\le\Delta+vn\}\).
For \(v\ge0\), an upper bound \(q\) for its tilted probability is also an
upper bound for the tilted probability that
\(\operatorname{prependHistory}(x,\operatorname{history}_n(x+y,z))\)
lies in the affine corridor with terminal cutoff.

This transfer supplies the corridor estimate used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.5.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open ProbabilityTheory.RandomWalk

/-- The probability of a child continuation in an endpoint-truncated affine
corridor is bounded by the corresponding drawdown-and-endpoint probability.
The pathwise event inclusion transfers any available drawdown estimate to the
corridor probability used by the affine-tube second-moment recursion. -/
theorem tiltedIncrementFieldLaw_affineCorridorHistoryEndpointCutoff_le_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (x lower drift width endpointUpper y : ℝ)
    (hdrift : 0 ≤ drift) (q : ℝ≥0∞)
    (hdrawdown : (tiltedIncrementFieldLaw φ μ)
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ))) ≤ q) :
    (tiltedIncrementFieldLaw φ μ)
      {increment | prependHistory x
        (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
          affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper} ≤ q := by
  apply le_trans (measure_mono ?_) hdrawdown
  intro increment hcutoff
  exact affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent
    n x lower drift width y hdrift increment hcutoff.1

end ProbabilityTheory.BranchingRandomWalk.Spine

end
