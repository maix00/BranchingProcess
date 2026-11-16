/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Spine.Tube.MRCA.Expansion
import Probability.Process.RandomWalk.Path.Block.Law.Basic
import Probability.Process.RandomWalk.Path.Block.Partition.Basic
import Probability.Sequence.IID.Blocks.Prefix
import Probability.Process.RandomWalk.Path.Window.Core
import Probability.Process.RandomWalk.Path.Window.Endpoint
import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomain
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.FinitePath

/-!
# Entrance and bridge composition for the second-stage corridor

## Internal proof declarations


The proof-chain lemma used in `SecondStage/Lemmas/Corridor/AffineBound.lean`,
`iidSequenceLaw_measure_ge_mul_of_finiteMovingEntrance_downwardBridge`, proves
the block-product estimate
\[
  \mathbb P_\nu(A_{\mathrm{entrance}})\,
  \mathbb P_\nu(A_{\mathrm{bridge}})
  \le \mathbb P_\nu(A_{\mathrm{affine}}),
\]
where the first block follows the affine lower boundary and the second block
stays in a fixed downward corridor. The endpoint margins imply that the two
block events together are contained in the full affine-corridor event.
-/

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.BranchingRandomWalk.Spine

private lemma partialSum_prefixBlock_eq_displacement
    {prefixLength : ℕ} (increment : ℕ → ℝ)
    (j : Fin (prefixLength + 1)) :
    Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j =
      AdditivePath.displacement j.val increment := by
  rw [RandomWalk.partialSum_blockCoordinates,
    AdditivePath.blockSum_eq_displacement_natAdd]
  simp

private lemma blockCoordinates_sum_eq_blockSum
    {length : ℕ} (start : ℕ) (increment : ℕ → ℝ) :
    (∑ j : Fin length, Combinatorics.Sequence.blockCoordinates start length increment j) =
      AdditivePath.blockSum start length increment := by
  rw [Finset.sum_fin_eq_sum_range,
    AdditivePath.blockSum_eq_displacement_natAdd]
  unfold AdditivePath.displacement
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Combinatorics.Sequence.blockCoordinates, Finset.mem_range.mp hi]

/-- The prefix entrance followed by a downward bridge lies in the full
affine corridor. The bridge interval may be chosen independently of the
prefix endpoint; the four scalar inequalities are the deterministic tube
geometry needed for the splice. -/
private lemma finiteMovingEntrance_and_downwardBridge_mem_affineCorridorThrough
    (horizon prefixLength bridgeLength : ℕ)
    (hpartition : prefixLength + bridgeLength = horizon)
    (entranceScale drift width terminalExtra bridgeLower bridgeUpper
      bridgeEndpointLower bridgeEndpointUpper : ℝ)
    (hscale : 0 < entranceScale) (hdrift : 0 ≤ drift)
    (hentranceWidth : entranceScale ≤ width)
    (hbridgeLower : entranceScale / 3 + bridgeLower ≥
      drift * (bridgeLength : ℝ))
    (hbridgeUpper : 2 * entranceScale / 3 + bridgeUpper ≤ width)
    (hterminal : 2 * entranceScale / 3 + bridgeEndpointUpper ≤
      drift * (bridgeLength : ℝ) + terminalExtra)
    (increment : ℕ → ℝ)
    (hentrance : Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
      finiteMovingEntranceEvent (n := prefixLength) entranceScale
        (drift / entranceScale) 0)
    (hbridge : FiniteInClosedIntervalEndsIn bridgeLower bridgeUpper
      bridgeEndpointLower bridgeEndpointUpper 0
      (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment)) :
    RandomWalk.history horizon 0 increment ∈
      affineCorridorThrough horizon 0 drift width
        (drift * (horizon : ℝ) + terminalExtra) := by
  have hentranceSpec :=
    (mem_finiteMovingEntranceEvent_iff entranceScale
      (drift / entranceScale) 0
      (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)).mp hentrance
  have hprefix (j : Fin (prefixLength + 1)) :
      drift * (j.val : ℝ) ≤ AdditivePath.displacement j.val increment ∧
        AdditivePath.displacement j.val increment ≤
          entranceScale + drift * (j.val : ℝ) := by
    have hj : finiteNormalizedStepKnots entranceScale
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j ∈
        Set.Icc (drift / entranceScale * (j.val : ℝ))
          (1 + drift / entranceScale * (j.val : ℝ)) := by
      simpa [finiteNormalizedStepKnots] using hentranceSpec.1 j
    have hsum := partialSum_prefixBlock_eq_displacement increment j
    rw [finiteNormalizedStepKnots, hsum] at hj
    rcases Set.mem_Icc.mp hj with ⟨hlo, hhi⟩
    have hinv : entranceScale *
        (entranceScale⁻¹ * AdditivePath.displacement j.val increment) =
          AdditivePath.displacement j.val increment := by
      field_simp [hscale.ne']
    have hl := mul_le_mul_of_nonneg_left hlo hscale.le
    have hu := mul_le_mul_of_nonneg_left hhi hscale.le
    rw [hinv] at hl hu
    have hlEq : entranceScale *
        (drift / entranceScale * (j.val : ℝ)) = drift * (j.val : ℝ) := by
      field_simp
    have huEq : entranceScale *
        (1 + drift / entranceScale * (j.val : ℝ)) =
          entranceScale + drift * (j.val : ℝ) := by
      field_simp
    rw [hlEq] at hl
    rw [huEq] at hu
    exact ⟨hl, hu⟩
  have hprefixEnd (x : ℝ) (hx :
      x = AdditivePath.displacement prefixLength increment) :
      entranceScale / 3 + drift * (prefixLength : ℝ) ≤ x ∧
        x ≤ 2 * entranceScale / 3 + drift * (prefixLength : ℝ) := by
    have hend : finiteNormalizedStepKnots entranceScale
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
        (Fin.last prefixLength) ∈
        Set.Icc (1 / 3 + drift / entranceScale * (prefixLength : ℝ))
          (2 / 3 + drift / entranceScale * (prefixLength : ℝ)) := by
      simpa [finiteNormalizedStepKnots] using hentranceSpec.2
    have hlast :
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
          (Fin.last prefixLength) =
        AdditivePath.displacement prefixLength increment := by
      exact partialSum_prefixBlock_eq_displacement increment (Fin.last prefixLength)
    rw [finiteNormalizedStepKnots, hlast] at hend
    rcases Set.mem_Icc.mp hend with ⟨hlo, hhi⟩
    have hinv : entranceScale *
        (entranceScale⁻¹ * AdditivePath.displacement prefixLength increment) =
        AdditivePath.displacement prefixLength increment := by
      field_simp [hscale.ne']
    have hl := mul_le_mul_of_nonneg_left hlo hscale.le
    have hu := mul_le_mul_of_nonneg_left hhi hscale.le
    rw [hinv, ← hx] at hl hu
    have hlEq : entranceScale *
        (1 / 3 + drift / entranceScale * (prefixLength : ℝ)) =
          entranceScale / 3 + drift * (prefixLength : ℝ) := by
      field_simp
    have huEq : entranceScale *
        (2 / 3 + drift / entranceScale * (prefixLength : ℝ)) =
          2 * entranceScale / 3 + drift * (prefixLength : ℝ) := by
      field_simp
    rw [hlEq] at hl
    rw [huEq] at hu
    exact ⟨hl, hu⟩
  have hbridgePath (j : Fin (bridgeLength + 1)) :
      bridgeLower ≤ AdditivePath.blockSum prefixLength j.val increment ∧
        AdditivePath.blockSum prefixLength j.val increment ≤ bridgeUpper := by
    have hpath : InClosedInterval bridgeLower bridgeUpper bridgeLength 0
        (fun k => increment (prefixLength + k)) :=
      (RandomWalk.finiteInClosedInterval_blockCoordinates_iff
        bridgeLower bridgeUpper 0 prefixLength bridgeLength increment).mp hbridge.1
    have hj : RandomWalk.history bridgeLength 0
        (fun k => increment (prefixLength + k)) j ∈
        Set.Icc bridgeLower bridgeUpper := by
      simpa only [InClosedInterval, InWindows] using hpath j
    simp only [RandomWalk.history_apply, zero_add] at hj
    rw [← AdditivePath.blockSum_eq_displacement_natAdd prefixLength j.val increment] at hj
    exact Set.mem_Icc.mp hj
  have hbridgeEnd :
      AdditivePath.blockSum prefixLength bridgeLength increment ≤
        bridgeEndpointUpper := by
    have hend := hbridge.2
    rw [blockCoordinates_sum_eq_blockSum prefixLength increment] at hend
    have hend' : 0 + AdditivePath.blockSum prefixLength bridgeLength increment ∈
        Set.Icc bridgeEndpointLower bridgeEndpointUpper := by
      simpa only [zero_add] using hend
    simpa only [zero_add] using (Set.mem_Icc.mp hend').2
  change (∀ k : Fin (horizon + 1),
      0 + drift * (k.val : ℝ) ≤ RandomWalk.history horizon 0 increment k ∧
        RandomWalk.history horizon 0 increment k ≤
          0 + drift * (k.val : ℝ) + width) ∧
    RandomWalk.history horizon 0 increment (Fin.last horizon) ≤
      drift * (horizon : ℝ) + terminalExtra
  simp only [zero_add]
  constructor
  · intro k
    by_cases hk : k.val ≤ prefixLength
    · let j : Fin (prefixLength + 1) := ⟨k.val, by omega⟩
      have hj := hprefix j
      have hval : j.val = k.val := rfl
      have hwidth : entranceScale + drift * (k.val : ℝ) ≤
          width + drift * (k.val : ℝ) := by
        linarith [hentranceWidth]
      have hupper : AdditivePath.displacement j.val increment ≤
          drift * (k.val : ℝ) + width := by
        calc
          AdditivePath.displacement j.val increment ≤
              entranceScale + drift * (k.val : ℝ) := by simpa [hval] using hj.2
          _ ≤ width + drift * (k.val : ℝ) := hwidth
          _ = drift * (k.val : ℝ) + width := by ring
      have hpoint := And.intro (by simpa [hval] using hj.1) hupper
      have hpoint' :
          drift * (k.val : ℝ) ≤ AdditivePath.displacement k.val increment ∧
            AdditivePath.displacement k.val increment ≤
              drift * (k.val : ℝ) + width := by
        simpa [hval] using hpoint
      simpa only [RandomWalk.history_apply, zero_add] using hpoint'
    · have hk' : prefixLength < k.val := Nat.lt_of_not_ge hk
      let j : Fin (bridgeLength + 1) :=
        ⟨k.val - prefixLength, by omega⟩
      have hjLe : j.val ≤ bridgeLength := Nat.le_of_lt_succ j.isLt
      have hkval : k.val = prefixLength + j.val := by
        dsimp [j]
        omega
      have hkvalReal : (k.val : ℝ) = (prefixLength : ℝ) + (j.val : ℝ) := by
        exact_mod_cast hkval
      have hx := hprefixEnd (AdditivePath.displacement prefixLength increment) rfl
      have hb := hbridgePath j
      have hsplit : AdditivePath.displacement k.val increment =
          AdditivePath.displacement prefixLength increment +
            AdditivePath.blockSum prefixLength j.val increment := by
        rw [hkval, AdditivePath.displacement_add_eq_add_blockSum]
      have hpoint :
          drift * (k.val : ℝ) ≤ AdditivePath.displacement k.val increment ∧
            AdditivePath.displacement k.val increment ≤
              drift * (k.val : ℝ) + width := by
        rw [hsplit]
        have hjCast : (j.val : ℝ) ≤ (bridgeLength : ℝ) := by exact_mod_cast hjLe
        have htimeSum :
            drift * (prefixLength : ℝ) + drift * (j.val : ℝ) =
              drift * (k.val : ℝ) := by
          rw [hkvalReal]
          ring
        constructor
        · have hlengthLower :=
            add_le_add_right hbridgeLower (drift * (prefixLength : ℝ))
          have htime := mul_le_mul_of_nonneg_left hjCast hdrift
          nlinarith [hx.1, hb.1, htime, hlengthLower, htimeSum]
        · have hupperTube := add_le_add_right hbridgeUpper
            (drift * (prefixLength : ℝ))
          have htime : 0 ≤ drift * (j.val : ℝ) :=
            mul_nonneg hdrift (Nat.cast_nonneg _)
          rw [← htimeSum]
          nlinarith [hx.2, hb.2, hupperTube, htime]
      simpa only [RandomWalk.history_apply, zero_add] using hpoint
  · have hx := hprefixEnd (AdditivePath.displacement prefixLength increment) rfl
    have hb := hbridgeEnd
    have hsplit : AdditivePath.displacement horizon increment =
        AdditivePath.displacement prefixLength increment +
          AdditivePath.blockSum prefixLength bridgeLength increment := by
      rw [← hpartition, AdditivePath.displacement_add_eq_add_blockSum]
    have hendpoint : AdditivePath.displacement horizon increment ≤
        drift * (horizon : ℝ) + terminalExtra := by
      rw [hsplit, ← hpartition, Nat.cast_add]
      nlinarith [hx.2, hb]
    simpa only [RandomWalk.history_apply, zero_add, Fin.val_last] using hendpoint

/-- The two finite blocks' probabilities multiply, and their intersection is
contained in the affine corridor event. -/
lemma iidSequenceLaw_measure_ge_mul_of_finiteMovingEntrance_downwardBridge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (horizon prefixLength bridgeLength : ℕ)
    (hpartition : prefixLength + bridgeLength = horizon)
    (entranceScale drift width terminalExtra bridgeLower bridgeUpper
      bridgeEndpointLower bridgeEndpointUpper : ℝ)
    (hscale : 0 < entranceScale) (hdrift : 0 ≤ drift)
    (hentranceWidth : entranceScale ≤ width)
    (hbridgeLower : entranceScale / 3 + bridgeLower ≥
      drift * (bridgeLength : ℝ))
    (hbridgeUpper : 2 * entranceScale / 3 + bridgeUpper ≤ width)
    (hterminal : 2 * entranceScale / 3 + bridgeEndpointUpper ≤
      drift * (bridgeLength : ℝ) + terminalExtra)
    (entryMass bridgeMass : ℝ≥0∞)
    (hentry : entryMass ≤ iidSequenceLaw ν
      {increment | Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
        finiteMovingEntranceEvent (n := prefixLength) entranceScale
          (drift / entranceScale) 0})
    (hbridge : bridgeMass ≤ iidSequenceLaw ν
      {increment | FiniteInClosedIntervalEndsIn bridgeLower bridgeUpper
        bridgeEndpointLower bridgeEndpointUpper 0
        (Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment)}) :
    entryMass * bridgeMass ≤ iidSequenceLaw ν
      {increment | RandomWalk.history horizon 0 increment ∈
        affineCorridorThrough horizon 0 drift width
          (drift * (horizon : ℝ) + terminalExtra)} := by
  let entrance : Set (Fin prefixLength → ℝ) :=
    finiteMovingEntranceEvent (n := prefixLength) entranceScale
      (drift / entranceScale) 0
  let bridge : Set (Fin bridgeLength → ℝ) :=
    {block | FiniteInClosedIntervalEndsIn bridgeLower bridgeUpper
      bridgeEndpointLower bridgeEndpointUpper 0 block}
  let fullHorizonCorridorEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history horizon 0 increment ∈
      affineCorridorThrough horizon 0 drift width
        (drift * (horizon : ℝ) + terminalExtra)}
  have hentranceMeasurable : MeasurableSet entrance := by
    simpa [entrance] using measurableSet_finiteMovingEntranceEvent
      (n := prefixLength) entranceScale (drift / entranceScale) 0
  have hbridgeMeasurable : MeasurableSet bridge :=
    measurableSet_finiteInClosedIntervalEndsIn bridgeLower bridgeUpper
      bridgeEndpointLower bridgeEndpointUpper 0 bridgeLength
  have hprefix : MeasurableSet[sequencePrefixFiltration (E := ℝ) prefixLength]
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ entrance} := by
    rw [sequencePrefixFiltration_eq_comap_blockCoordinates prefixLength]
    exact (MeasurableSpace.measurableSet_comap).2
      ⟨entrance, hentranceMeasurable, rfl⟩
  have hfactor := iidSequenceLaw_measure_prefix_inter_block_eq_mul
    ν prefixLength bridgeLength
    {increment : ℕ → ℝ |
      Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ entrance}
    hprefix bridge hbridgeMeasurable
  have hsubset :
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ entrance ∧
          Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength
            increment ∈ bridge} ⊆ fullHorizonCorridorEvent := by
    intro increment hevent
    exact finiteMovingEntrance_and_downwardBridge_mem_affineCorridorThrough
      horizon prefixLength bridgeLength hpartition entranceScale drift width
      terminalExtra bridgeLower bridgeUpper bridgeEndpointLower bridgeEndpointUpper
      hscale hdrift
      hentranceWidth hbridgeLower hbridgeUpper hterminal increment hevent.1 hevent.2
  calc
    entryMass * bridgeMass ≤
        iidSequenceLaw ν
          {increment | Combinatorics.Sequence.blockCoordinates 0 prefixLength
            increment ∈ entrance} *
          iidSequenceLaw ν
            {increment | Combinatorics.Sequence.blockCoordinates 0 bridgeLength
              increment ∈ bridge} := mul_le_mul' hentry hbridge
    _ = iidSequenceLaw ν
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ entrance ∧
            Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength
              increment ∈ bridge} := hfactor.symm
    _ ≤ iidSequenceLaw ν fullHorizonCorridorEvent := measure_mono hsubset
    _ = _ := rfl

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
