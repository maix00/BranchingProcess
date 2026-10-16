/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.JumpPattern.Setup
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Horizontal.PathSegment

/-!
# Geometry of the rounded-maximum decomposition

The proof-specific declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownBlockTubeCondition` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownBlockTubeCondition_implies_tubeBlockEvent`: on block $j$,
  $M_j-w-\delta<S_{s_j+k}\le M_j$ implies the corresponding conditional
  tube event.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_card_maximumJumpSet_le` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_discretizedMaximumBlockDecomposition`: the rounded maximum has at
  most the permitted number of jumps, and its increments decompose into the
  blockwise path increments.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_le_threshold_add_delta_of_noLargeDrop` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.neg_delta_le_additivePath_of_noLargeDrop`: the no-large-drop condition
  gives the upper and lower path bounds used in the block construction.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_event_discretizedMaximumBlockDecomposition` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_event_goodBlocks_satisfy_tubeCondition`: a path in the drawdown
  event has the required blockwise decomposition and every non-jump block
  satisfies its rounded-maximum tube condition.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownJumpPatternTubeIntersection`, `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownAdmissibleJumpPatterns`,
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_mem_jumpPatternTubeIntersection_of_goodBlocks`, and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdown_noLargeDropEvent_subset_jumpPatternUnion`: the event is covered
  by the finite union of tube intersections indexed by admissible jump
  patterns.

These steps follow Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

def drawdownBlockTubeCondition
    (upper width delta : ℝ) (path : ℕ → ℝ)
    (remainder blockLength : ℕ) (j : ℕ) : Prop :=
  ∀ k ≤ blockLength,
    drawdownDiscretizedMaximum upper width path remainder blockLength j -
        width - delta < path (drawdownBlockStart remainder blockLength j + k) ∧
      path (drawdownBlockStart remainder blockLength j + k) ≤
        drawdownDiscretizedMaximum upper width path remainder blockLength j

/-- The deterministic tube condition on a block implies membership in the
corresponding conditional tube event centered at the rounded running maximum
of the past. -/
lemma drawdownBlockTubeCondition_implies_tubeBlockEvent
    (increment : ℕ → ℝ) (upper binWidth delta : ℝ)
    (remainder blockLength j : ℕ)
    (hcondition : drawdownBlockTubeCondition upper binWidth delta
      (AdditivePath.displacement · increment)
      remainder blockLength j) :
    increment ∈ drawdownTubeBlockEvent
      (drawdownBlockStart remainder blockLength j) blockLength
      (drawdownPastDiscretizedMaximum
        (start := drawdownBlockStart remainder blockLength j)
        upper binWidth)
      (binWidth + delta) := by
  apply (drawdownTubeBlockEvent_iff_path_in_interval
    (drawdownBlockStart remainder blockLength j) blockLength upper
    binWidth (binWidth + delta) increment).2
  intro k
  have hcenter :
      drawdownPastDiscretizedMaximum
          (start := drawdownBlockStart remainder blockLength j)
          upper binWidth
          (Combinatorics.Sequence.blockCoordinates 0
            (drawdownBlockStart remainder blockLength j) increment) =
        spatialBinLevel upper binWidth
          (AdditivePath.displacement · increment)
          (drawdownBlockStart remainder blockLength j) :=
    drawdownPastDiscretizedMaximum_eq_runningMaximum
      (drawdownBlockStart remainder blockLength j) upper binWidth increment
  have htube := hcondition (k : ℕ) (Nat.le_of_lt_succ k.isLt)
  have htube' := htube
  simp only [drawdownDiscretizedMaximum] at htube'
  rw [← hcenter] at htube'
  rw [← hcenter]
  simp only [Set.mem_Icc]
  constructor
  · nlinarith [htube'.1]
  · exact htube'.2

/-- A nonincreasing discretized running maximum has at most `K + 1` jump
indices when its levels are encoded by `K + 1` possible grid indices. -/
lemma drawdown_card_maximumJumpSet_le {q K : ℕ}
    (bins : Fin (q + 1) → Fin (K + 1))
    (hmono : ∀ i j, i ≤ j → bins j ≤ bins i) :
    (drawdownMaximumJumpSet bins).card ≤ K + 1 := by
  exact card_spatialBinJumpSet_le bins hmono

/-- On the event in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3, the running maximum
can be rounded to a nondecreasing sequence of finitely many levels. Every
block with unchanged level is contained in the interval
`(M_j - width - delta, M_j]`.

The sequence is encoded by its grid indices, so `hmono` states that the
indices are nonincreasing. The last component is the tube inclusion used in
the conditional-expectation step of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3. -/
lemma drawdown_discretizedMaximumBlockDecomposition
    (increment : ℕ → ℝ) (horizon remainder blocks blockLength : ℕ)
    (upper width delta : ℝ)
    (hzero : AdditivePath.displacement 0 increment = 0)
    (hwidth : 0 < width)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta)
    (hupper : ∀ i ≤ horizon,
      AdditivePath.displacement i increment ≤ upper)
    (hblocks : remainder + blocks * blockLength ≤ horizon) :
    ∃ bins : Fin (blocks + 1) → Fin (⌊upper / width⌋₊ + 1),
      (∀ i j, i ≤ j → bins j ≤ bins i) ∧
      (∀ j, (bins j : ℕ) = spatialBinIndex upper width
        (AdditivePath.displacement · increment)
        (drawdownBlockStart remainder blockLength j.val)) ∧
      (∀ j : Fin blocks,
        bins j.castSucc = bins j.succ →
        ∀ k ≤ blockLength,
          drawdownDiscretizedMaximum upper width
              (AdditivePath.displacement · increment)
              remainder blockLength j.val - width - delta <
            AdditivePath.displacement
              (drawdownBlockStart remainder blockLength j.val + k) increment ∧
          AdditivePath.displacement
              (drawdownBlockStart remainder blockLength j.val + k) increment ≤
            drawdownDiscretizedMaximum upper width
              (AdditivePath.displacement · increment)
              remainder blockLength j.val) := by
  simpa only [drawdownBlockStart, drawdownDiscretizedMaximum] using
    exists_spatialBinSequence_for_noLargeDrop
      (AdditivePath.displacement · increment) upper width delta
      hzero hwidth hnoDrop hupper hblocks

/-- A no-large-drawdown path whose endpoint is below a threshold stays below
that threshold plus one drawdown allowance throughout the finite horizon. -/
lemma additivePath_le_threshold_add_delta_of_noLargeDrop
    {horizon : ℕ} (increment : ℕ → ℝ) (delta threshold : ℝ)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta)
    (hendpoint : AdditivePath.displacement horizon increment ≤ threshold) :
    ∀ i ≤ horizon,
      AdditivePath.displacement i increment ≤ threshold + delta := by
  intro i hi
  have h := hnoDrop i horizon hi (Nat.le_refl _)
  linarith

/-- Starting from zero, a no-large-drawdown path cannot descend below minus
the drawdown allowance. -/
lemma neg_delta_le_additivePath_of_noLargeDrop
    {horizon : ℕ} (increment : ℕ → ℝ) (delta : ℝ)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta)
    {i : ℕ} (hi : i ≤ horizon) :
    -delta ≤ AdditivePath.displacement i increment := by
  have h := hnoDrop 0 i (Nat.zero_le _) hi
  have hzero : AdditivePath.displacement 0 increment = 0 :=
    AdditivePath.displacement_zero increment
  rw [hzero] at h
  linarith

/-- Every path in `noLargeDropEndpointBelowEvent` has the discretized
running-maximum decomposition of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3. The
endpoint condition supplies the deterministic ceiling `threshold + delta`;
the drawdown condition supplies the lower side of each unchanged-maximum
block interval. -/
lemma drawdown_event_discretizedMaximumBlockDecomposition
    (increment : ℕ → ℝ) (horizon remainder blocks blockLength : ℕ)
    (delta threshold width : ℝ) (hwidth : 0 < width)
    (hblocks : remainder + blocks * blockLength ≤ horizon)
    (hevent : increment ∈
      noLargeDropEndpointBelowEvent horizon delta threshold) :
    ∃ bins : Fin (blocks + 1) → Fin
        (⌊(threshold + delta) / width⌋₊ + 1),
      (∀ i j, i ≤ j → bins j ≤ bins i) ∧
      (∀ j, (bins j : ℕ) = spatialBinIndex (threshold + delta) width
        (AdditivePath.displacement · increment)
        (drawdownBlockStart remainder blockLength j.val)) ∧
      (∀ j : Fin blocks,
        bins j.castSucc = bins j.succ →
        ∀ k ≤ blockLength,
          drawdownDiscretizedMaximum (threshold + delta) width
              (AdditivePath.displacement · increment)
              remainder blockLength j.val - width - delta <
            AdditivePath.displacement
              (drawdownBlockStart remainder blockLength j.val + k) increment ∧
          AdditivePath.displacement
              (drawdownBlockStart remainder blockLength j.val + k) increment ≤
            drawdownDiscretizedMaximum (threshold + delta) width
              (AdditivePath.displacement · increment)
              remainder blockLength j.val) := by
  rcases hevent with ⟨hnoDrop, hendpoint⟩
  have hzero : AdditivePath.displacement 0 increment = 0 :=
    AdditivePath.displacement_zero increment
  have hupper : ∀ i ≤ horizon,
      AdditivePath.displacement i increment ≤ threshold + delta :=
    additivePath_le_threshold_add_delta_of_noLargeDrop
      increment delta threshold hnoDrop hendpoint
  exact drawdown_discretizedMaximumBlockDecomposition
    increment horizon remainder blocks blockLength (threshold + delta)
    width delta hzero hwidth hnoDrop hupper hblocks

/-- On a drawdown event, the rounded maximum has a bounded jump set, and
every block outside that set satisfies the fixed-interval condition in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3. This packages the deterministic reduction
preceding its conditional-expectation iteration. -/
lemma drawdown_event_goodBlocks_satisfy_tubeCondition
    (increment : ℕ → ℝ) (horizon remainder blocks blockLength : ℕ)
    (delta threshold width : ℝ) (hwidth : 0 < width)
    (hblocks : remainder + blocks * blockLength ≤ horizon)
    (hevent : increment ∈
      noLargeDropEndpointBelowEvent horizon delta threshold) :
    (drawdownRunningMaximumJumpSet (q := blocks) (threshold + delta) width
      (fun j : Fin (blocks + 1) => drawdownBlockStart remainder blockLength j.val)
      hwidth increment).card ≤ ⌊(threshold + delta) / width⌋₊ + 1 ∧
      ∀ j : Fin blocks,
        j ∉ drawdownRunningMaximumJumpSet (q := blocks) (threshold + delta) width
          (fun i : Fin (blocks + 1) => drawdownBlockStart remainder blockLength i.val)
          hwidth increment →
        drawdownBlockTubeCondition (threshold + delta) width delta
          (AdditivePath.displacement · increment)
          remainder blockLength j.val := by
  obtain ⟨bins, hmono, hindex, htube⟩ :=
    drawdown_event_discretizedMaximumBlockDecomposition
      increment horizon remainder blocks blockLength delta threshold width
      hwidth hblocks hevent
  let starts : Fin (blocks + 1) → ℕ :=
    fun j => drawdownBlockStart remainder blockLength (j : ℕ)
  have hbins : bins = drawdownRunningMaximumBins (threshold + delta)
      width starts hwidth increment := by
    funext j
    apply Fin.ext
    simpa [drawdownRunningMaximumBins, starts] using hindex j
  have hjumps : drawdownMaximumJumpSet bins =
      drawdownRunningMaximumJumpSet (q := blocks) (threshold + delta) width
        starts hwidth increment := by
    simp [drawdownMaximumJumpSet, drawdownRunningMaximumJumpSet, hbins]
  refine ⟨?_, ?_⟩
  · rw [← hjumps]
    exact drawdown_card_maximumJumpSet_le bins hmono
  · intro j hj
    have hj' : j ∉ drawdownMaximumJumpSet bins := by
      simpa [hjumps] using hj
    have hsame : bins j.castSucc = bins j.succ := by
      by_contra hne
      apply hj'
      simp [drawdownMaximumJumpSet, spatialBinJumpSet, hne]
    simpa [drawdownBlockTubeCondition] using htube j hsame

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

/-- If the pattern is the actual jump set of the rounded running maximum,
every block tube required by that pattern holds whenever its deterministic
good-block condition holds. -/
lemma drawdown_mem_jumpPatternTubeIntersection_of_goodBlocks
    {q : ℕ} (increment : ℕ → ℝ)
    (remainder blockLength : ℕ) (upper binWidth delta : ℝ)
    (hbinWidth : 0 < binWidth) (pattern : Finset (Fin q))
    (hpattern : pattern = drawdownRunningMaximumJumpSet upper binWidth
      (fun j : Fin (q + 1) => drawdownBlockStart remainder blockLength j.val)
      hbinWidth increment)
    (hgood : ∀ j : Fin q,
      j ∉ drawdownRunningMaximumJumpSet upper binWidth
        (fun i : Fin (q + 1) => drawdownBlockStart remainder blockLength i.val)
        hbinWidth increment →
      drawdownBlockTubeCondition upper binWidth delta
        (AdditivePath.displacement · increment) remainder blockLength j.val) :
    increment ∈ drawdownJumpPatternTubeIntersection remainder blockLength
      pattern upper binWidth (binWidth + delta) := by
  let jumps := drawdownRunningMaximumJumpSet upper binWidth
    (fun j : Fin (q + 1) => drawdownBlockStart remainder blockLength j.val)
    hbinWidth increment
  let events := drawdownJumpPatternTubeEvent remainder blockLength pattern
    upper binWidth (binWidth + delta)
  have hprefix : ∀ n : ℕ, n ≤ q →
      increment ∈ ProbabilityTheory.conditionalBlockIntersection events n := by
    intro n hn
    induction n with
    | zero => simp [ProbabilityTheory.conditionalBlockIntersection]
    | succ n ih =>
        rw [ProbabilityTheory.conditionalBlockIntersection]
        constructor
        · exact ih (by omega)
        · have hnq : n < q := by omega
          let j : Fin q := ⟨n, hnq⟩
          by_cases hjump : j ∈ pattern
          · simp [events, drawdownJumpPatternTubeEvent, hnq, hjump, j]
          · have hnotJump : j ∉ jumps := by
              simpa [hpattern, jumps] using hjump
            have hblock := hgood j hnotJump
            have htube := drawdownBlockTubeCondition_implies_tubeBlockEvent
              increment upper binWidth delta remainder blockLength j.val hblock
            simpa [events, drawdownJumpPatternTubeEvent, hnq, hjump, j,
              drawdownBlockStart] using htube
  exact hprefix q le_rfl

/-- Every path in the drawdown event belongs to a tube intersection for one
of the finitely many jump patterns allowed by the discretized-maximum
decomposition in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.3. -/
lemma drawdown_noLargeDropEvent_subset_jumpPatternUnion
    (increment : ℕ → ℝ) (horizon blockLength : ℕ)
    (delta threshold binWidth : ℝ) (hbinWidth : 0 < binWidth)
    (hevent : increment ∈
      noLargeDropEndpointBelowEvent horizon delta threshold) :
    increment ∈ ⋃ pattern ∈ drawdownAdmissibleJumpPatterns
        (horizon / blockLength)
        (⌊(threshold + delta) / binWidth⌋₊ + 1),
      drawdownJumpPatternTubeIntersection
        (horizon % blockLength) blockLength pattern
        (threshold + delta) binWidth (binWidth + delta) := by
  classical
  let q := horizon / blockLength
  let remainder := horizon % blockLength
  let starts : Fin (q + 1) → ℕ := fun j =>
    drawdownBlockStart remainder blockLength j.val
  let jumps := drawdownRunningMaximumJumpSet (threshold + delta) binWidth
    starts hbinWidth increment
  have hblocks : remainder + q * blockLength ≤ horizon := by
    apply le_of_eq
    simpa [q, remainder, Nat.mul_comm] using
      (Nat.mod_add_div horizon blockLength)
  obtain ⟨hcard, hgood⟩ := drawdown_event_goodBlocks_satisfy_tubeCondition
    increment horizon remainder q blockLength delta threshold binWidth
    hbinWidth hblocks hevent
  have hpattern : jumps = drawdownRunningMaximumJumpSet
      (threshold + delta) binWidth
      (fun j : Fin (q + 1) => drawdownBlockStart remainder blockLength j.val)
      hbinWidth increment := by
    rfl
  have hcard' : jumps.card ≤ ⌊(threshold + delta) / binWidth⌋₊ + 1 := by
    simpa [jumps, starts] using hcard
  have hpatternAdmissible : jumps ∈ drawdownAdmissibleJumpPatterns q
      (⌊(threshold + delta) / binWidth⌋₊ + 1) := by
    simp [drawdownAdmissibleJumpPatterns, hcard']
  have hgood' : ∀ j : Fin q, j ∉ jumps →
      drawdownBlockTubeCondition (threshold + delta) binWidth delta
        (AdditivePath.displacement · increment) remainder blockLength j.val := by
    simpa [jumps, starts] using hgood
  refine Set.mem_iUnion.2 ⟨jumps, Set.mem_iUnion.2 ?_⟩
  refine ⟨hpatternAdmissible, ?_⟩
  exact drawdown_mem_jumpPatternTubeIntersection_of_goodBlocks
    increment remainder blockLength (threshold + delta) binWidth delta
    hbinWidth jumps (by simp [jumps, starts]) hgood'

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
