/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Reflection
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Inclusion

/-!
# Staircase inclusion for an upper terminal window

The module-visible supporting lemma in this file is:

- `initialInterTubeBlocks_subset_driftedTubeUpperEndpointWindowEvent`:
  if each horizontal block is inside the tilted tube and the last
  endpoint window is contained in both the full terminal tube and
  $[s_L-v\Delta,s_L]$, then the staircase event is contained in the
  upper-endpoint event.

This is the symmetric terminal-window inclusion in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The common staircase path and a final upper-edge window imply the
upper-endpoint tilted-tube event. The path inclusion uses the same
horizontal-block argument as the lower-endpoint case. -/
lemma initialInterTubeBlocks_subset_driftedTubeUpperEndpointWindowEvent
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (q horizon : ℕ) (hq : 0 < q)
    (hfinish : start q = horizon)
    (initial : Set (ℕ → ℝ))
    (width drift base endpointFraction : ℝ)
    (blockLower blockWidth v₁ v₂ : ℕ → ℝ)
    (hblockLower : ∀ j, j < q →
      blockLower j = base +
        max (drift * (start j : ℝ) / width ^ 2)
          (drift * ((start j + length j : ℕ) : ℝ) / width ^ 2))
    (hblockUpper : ∀ j, j < q →
      blockLower j + blockWidth j = base +
        min (drift * (start j : ℝ) / width ^ 2)
          (drift * ((start j + length j : ℕ) : ℝ) / width ^ 2) + width)
    (hentrance : ∀ increment ∈ initial, ∀ time : ℕ,
      1 ≤ time → time ≤ start 0 →
        base + drift * (time : ℝ) / width ^ 2 ≤
          AdditivePath.displacement time increment ∧
        AdditivePath.displacement time increment ≤
          base + drift * (time : ℝ) / width ^ 2 + width)
    (hfinalFull :
      Set.Icc
        (blockLower (q - 1) + v₁ (q - 1) * blockWidth (q - 1))
        (blockLower (q - 1) + v₂ (q - 1) * blockWidth (q - 1)) ⊆
      Set.Icc (base + drift * (horizon : ℝ) / width ^ 2)
        (base + drift * (horizon : ℝ) / width ^ 2 + width))
    (hfinalUpper :
      Set.Icc
        (blockLower (q - 1) + v₁ (q - 1) * blockWidth (q - 1))
        (blockLower (q - 1) + v₂ (q - 1) * blockWidth (q - 1)) ⊆
      Set.Icc
        (base + drift * (horizon : ℝ) / width ^ 2 + width -
          endpointFraction * width)
        (base + drift * (horizon : ℝ) / width ^ 2 + width)) :
    initial ∩ conditionalBlockIntersection
      (fun j => tubeBlockEvent (start j) (length j)
        (blockLower j) (blockWidth j) (v₁ j) (v₂ j)) q ⊆
      driftedTubeUpperEndpointWindowEvent
        horizon width drift base endpointFraction := by
  have hfull :=
    initialInterTubeBlocks_subset_driftedTubeEndpointWindowEvent_of_extremeBounds
      start length hnext q horizon hq hfinish initial width drift base
      1 blockLower blockWidth v₁ v₂ hblockLower hblockUpper
      hentrance (by simpa using hfinalFull)
  intro increment hin
  have hpath := (hfull hin).1
  constructor
  · exact hpath
  · have hlast : q - 1 < q := by omega
    have hlastEnd : q - 1 + 1 = q := by omega
    have hlastBlock : increment ∈
        tubeBlockEvent (start (q - 1)) (length (q - 1))
          (blockLower (q - 1)) (blockWidth (q - 1))
          (v₁ (q - 1)) (v₂ (q - 1)) :=
      (mem_conditionalBlockIntersection_iff _ q increment).mp hin.2
        (q - 1) hlast
    have hlastPosition := tubeBlockEvent_end_mem hlastBlock
    rw [← hnext (q - 1), hlastEnd, hfinish] at hlastPosition
    exact hfinalUpper hlastPosition

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
