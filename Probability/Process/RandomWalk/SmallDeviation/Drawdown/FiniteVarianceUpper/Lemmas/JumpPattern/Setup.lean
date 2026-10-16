/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.ConditionalBlocks
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Rounded maxima and jump-pattern data

The proof-specific declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownBlockStart`: $s_j=r+j\ell$, the block-start schedule.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownDiscretizedMaximum`, `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownRunningMaximumBins`,
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownRunningMaximumJumpSet`, and `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownMaximumJumpSet`: the rounded
  running maximum $M_j$, its bin indices, and the block indices where those
  bins change.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownJumpPatternTubeEvent`: the intersection of the specified
  non-jump-block tube events for a fixed pattern.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownJumpPatternBound`, `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_prod_jumpPatternBound_eq_pow`, and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_prod_jumpPatternBound_le_pow`: the block factor equals $p$ on a
  non-jump and $1$ on a jump, so its product is $p^{q-|J|}$ and is at most
  $p^{q-K}$ when $|J|\le K$ and $0\le p\le1$.

These declarations support Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

def drawdownBlockStart (remainder blockLength j : ℕ) : ℕ :=
  remainder + j * blockLength

/-- The rounded running maximum `M_j` from the proof of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.3, at the start time of block `j`. -/
noncomputable def drawdownDiscretizedMaximum
    (upper width : ℝ) (path : ℕ → ℝ)
    (remainder blockLength : ℕ) (j : ℕ) : ℝ :=
  spatialBinLevel upper width path
    (drawdownBlockStart remainder blockLength j)

/-- The index set of blocks on which the discretized running maximum
changes. -/
def drawdownMaximumJumpSet {q K : ℕ}
    (bins : Fin (q + 1) → Fin (K + 1)) : Finset (Fin q) :=
  spatialBinJumpSet bins

/-- The spatial-bin indices of the running maximum at the block starts for a
fixed increment path. -/
noncomputable def drawdownRunningMaximumBins {q : ℕ}
    (upper width : ℝ) (starts : Fin (q + 1) → ℕ)
    (hwidth : 0 < width) (increment : ℕ → ℝ) :
    Fin (q + 1) → Fin (⌊upper / width⌋₊ + 1) := by
  intro j
  refine ⟨spatialBinIndex upper width
      (AdditivePath.displacement · increment) (starts j), ?_⟩
  exact Nat.lt_succ_of_le
    (spatialBinIndex_le_of_zero upper width
      (AdditivePath.displacement · increment) (starts j) hwidth
      (AdditivePath.displacement_zero increment))

/-- The jump indices of the discretized running maximum for one sample path. -/
noncomputable def drawdownRunningMaximumJumpSet {q : ℕ}
    (upper width : ℝ) (starts : Fin (q + 1) → ℕ)
    (hwidth : 0 < width) (increment : ℕ → ℝ) : Finset (Fin q) :=
  spatialBinJumpSet
    (drawdownRunningMaximumBins upper width starts hwidth increment)

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

/-- The factors for a fixed jump pattern multiply to the tube-bound factor
raised to the number of indices outside that pattern. -/
lemma drawdown_prod_jumpPatternBound_eq_pow {q : ℕ}
    (pattern : Finset (Fin q)) (p : ℝ) :
    (∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) =
      p ^ (q - pattern.card) := by
  classical
  rw [← Fin.prod_univ_eq_prod_range
    (fun n : ℕ => drawdownJumpPatternBound pattern p n) q]
  have hterm (j : Fin q) :
      drawdownJumpPatternBound pattern p j.val =
        if j ∈ pattern then 1 else p := by
    simp [drawdownJumpPatternBound]
  simp_rw [hterm]
  rw [Finset.prod_ite]
  have hnonjump :
      (Finset.univ.filter (fun j : Fin q => j ∉ pattern)).card =
        q - pattern.card := by
    rw [show Finset.univ.filter (fun j : Fin q => j ∉ pattern) =
      Finset.univ \ pattern by ext j; simp]
    rw [Finset.card_sdiff_of_subset pattern.subset_univ]
    simp
  simp [hnonjump]

/-- A jump pattern with at most `K` indices has at least `q-K` nonjump
indices, so its product is bounded by the corresponding power whenever the
one-block factor lies in `[0,1]`. -/
lemma drawdown_prod_jumpPatternBound_le_pow {q K : ℕ}
    (pattern : Finset (Fin q)) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcard : pattern.card ≤ K) :
    (∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
      p ^ (q - K) := by
  rw [drawdown_prod_jumpPatternBound_eq_pow]
  exact pow_le_pow_of_le_one hp0 hp1 (by omega)

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
