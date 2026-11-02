/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.ContinuousBoundary
public import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
import all Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Lemmas.ContinuousBoundary

/-!
# Measurability of terminal-left random-walk corridor events

For the normalized terminal-left path with $n>0$, cell $j<n$ carries the value
$S_j/x_n$ on $[j/n,(j+1)/n)$. Put
$b_{j,m}=(j+1)/n-1/(n+m+1)$ for $m\in\mathbb N$.

## Public declarations

- `measurableSet_terminalLeftNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet`:
  the inverse image of the moving continuous-boundary corridor under the
  terminal-left normalized path map is measurable in increment-sequence space.

Its finite-coordinate characterization and compact-cell estimates are
collected in `Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Lemmas.ContinuousBoundary`.

Compact subintervals exhaust each half-open terminal-left cell while retaining the
terminal value $S_{n-1}/x_n$ from Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open MeasureTheory
open Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Skorokhod
open Skorokhod.PathClass.StepCorridor

/-- For every number of steps, including zero, the exact continuous-corridor
preimage on the canonical increment space is measurable. -/
theorem measurableSet_terminalLeftNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet
    (lower upper : C(unitInterval, ℝ)) (scale : ℕ → ℝ) (n : ℕ) :
    MeasurableSet {increment : ℕ → ℝ |
      terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
        relativeContinuousBoundaryCorridorSet lower upper} := by
  by_cases hn : 0 < n
  · exact measurableSet_terminalLeftNormalizedStepCadlagPathIcc_preimage_relativeContinuousBoundaryCorridorSet_of_pos
      lower upper scale hn
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    by_cases hcorridor : ∀ t : unitInterval, lower t < 0 ∧ 0 < upper t
    · have heq : {increment : ℕ → ℝ |
          terminalLeftNormalizedStepCadlagPathIcc scale 0 increment ∈
            relativeContinuousBoundaryCorridorSet lower upper} = Set.univ := by
        ext increment
        constructor
        · intro _
          exact Set.mem_univ _
        · intro _
          refine ⟨terminalLeftPath_mem_space
            (normalizedStepCadlagPathIcc scale 0 increment), ?_⟩
          refine ⟨?_, ?_⟩
          · simp only [terminalLeftNormalizedStepCadlagPathIcc_zero]
          · intro t
            simpa only [terminalLeftNormalizedStepCadlagPathIcc_zero] using hcorridor t
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {increment : ℕ → ℝ |
          terminalLeftNormalizedStepCadlagPathIcc scale 0 increment ∈
            relativeContinuousBoundaryCorridorSet lower upper} = ∅ := by
        ext increment
        constructor
        · intro hpath
          change terminalLeftNormalizedStepCadlagPathIcc scale 0 increment ∈
            terminalLeftPathSpace ∧
              terminalLeftNormalizedStepCadlagPathIcc scale 0 increment ∈
                continuousBoundaryCorridorSet lower upper at hpath
          rcases hpath.2 with ⟨_, hbetween⟩
          apply hcorridor
          intro t
          simpa only [terminalLeftNormalizedStepCadlagPathIcc_zero] using hbetween t
        · simp
      rw [heq]
      exact MeasurableSet.empty

end ProbabilityTheory.RandomWalk

end
