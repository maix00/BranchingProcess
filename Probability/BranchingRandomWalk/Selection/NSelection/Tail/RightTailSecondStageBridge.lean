/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RightTailKilledCapacity
import Probability.Process.RandomWalk.Path.Block.Law
import Probability.Process.RandomWalk.Path.Block.Partition.Basic
import Probability.Process.RandomWalk.Path.Window
import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomain

/-!
# Entrance and bridge composition for the second-stage corridor

The finite-variance entrance event follows the affine lower boundary from
the tube's initial point. A later block can be restricted to a fixed
downward corridor. The endpoint margins below ensure both pieces stay in the
full affine tube and that their IID probabilities multiply.
-/

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- A finite increment block stays in a fixed interval and ends in a
specified interval. -/
def finiteCorridorBridgeEvent {n : ℕ}
    (lower upper endpointLower endpointUpper : ℝ) : Set (Fin n → ℝ) :=
  {block | (∀ j : Fin (n + 1),
      Fin.partialSum block j ∈ Set.Icc lower upper) ∧
    Fin.partialSum block (Fin.last n) ∈ Set.Icc endpointLower endpointUpper}

theorem measurableSet_finiteCorridorBridgeEvent {n : ℕ}
    (lower upper endpointLower endpointUpper : ℝ) :
    MeasurableSet (finiteCorridorBridgeEvent (n := n)
      lower upper endpointLower endpointUpper) := by
  unfold finiteCorridorBridgeEvent
  rw [show {block : Fin n → ℝ |
      (∀ j : Fin (n + 1), Fin.partialSum block j ∈ Set.Icc lower upper) ∧
        Fin.partialSum block (Fin.last n) ∈ Set.Icc endpointLower endpointUpper} =
      (⋂ j : Fin (n + 1),
        {block : Fin n → ℝ | Fin.partialSum block j ∈ Set.Icc lower upper}) ∩
        {block : Fin n → ℝ | Fin.partialSum block (Fin.last n) ∈
          Set.Icc endpointLower endpointUpper} by
      ext block
      simp]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    exact measurableSet_Icc.preimage (by fun_prop)
  · exact measurableSet_Icc.preimage (by fun_prop)

private theorem partialSum_prefixBlock_eq_displacement
    {prefixLength : ℕ} (increment : ℕ → ℝ)
    (j : Fin (prefixLength + 1)) :
    Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j =
      AdditivePath.displacement j.val increment := by
  rw [RandomWalk.partialSum_blockCoordinates,
    AdditivePath.blockSum_eq_displacement_natAdd]
  simp

private theorem history_coordinate_eq_displacement (n : ℕ)
    (increment : ℕ → ℝ) (i : Fin (n + 1)) :
    RandomWalk.history n 0 increment i = AdditivePath.displacement i.val increment := by
  rw [RandomWalk.history_eq_fromIncrements]
  simp [AdditivePath.fromIncrements, AdditivePath.displacement]

private theorem partialSum_nextBlock_eq_blockSum
    {prefixLength bridgeLength : ℕ} (increment : ℕ → ℝ)
    (j : Fin (bridgeLength + 1)) :
    Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) j =
      AdditivePath.blockSum prefixLength j.val increment :=
  RandomWalk.partialSum_blockCoordinates prefixLength increment j

/-- The prefix entrance followed by a downward bridge lies in the full
affine corridor. The bridge interval may be chosen independently of the
prefix endpoint; the four scalar inequalities are the deterministic tube
geometry needed for the splice. -/
theorem finiteMovingEntrance_and_downwardBridge_mem_affineCorridorThrough
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
    (hbridge : Combinatorics.Sequence.blockCoordinates prefixLength
      bridgeLength increment ∈
        finiteCorridorBridgeEvent (n := bridgeLength)
          bridgeLower bridgeUpper bridgeEndpointLower bridgeEndpointUpper) :
    RandomWalk.history horizon 0 increment ∈
      affineCorridorThrough horizon 0 drift width
        (drift * (horizon : ℝ) + terminalExtra) := by
  have hprefix (j : Fin (prefixLength + 1)) :
      drift * (j.val : ℝ) ≤ AdditivePath.displacement j.val increment ∧
        AdditivePath.displacement j.val increment ≤
          entranceScale + drift * (j.val : ℝ) := by
    have hj : finiteNormalizedStepKnots entranceScale
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j ∈
        Set.Icc (drift / entranceScale * (j.val : ℝ))
          (1 + drift / entranceScale * (j.val : ℝ)) := by
      simpa [finiteMovingEntranceEvent] using hentrance.1 j
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
      simpa [finiteMovingEntranceEvent] using hentrance.2
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
    have hj : 0 + Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) j ∈
        Set.Icc bridgeLower bridgeUpper := by
      simpa [FiniteInClosedInterval, Fin.partialSum] using hbridge.1 j
    have hsum := partialSum_nextBlock_eq_blockSum
      (prefixLength := prefixLength) increment j
    rw [hsum] at hj
    have hj' : AdditivePath.blockSum prefixLength j.val increment ∈
        Set.Icc bridgeLower bridgeUpper := by
      simpa only [zero_add] using hj
    exact Set.mem_Icc.mp hj'
  have hbridgeEnd :
      AdditivePath.blockSum prefixLength bridgeLength increment ≤
        bridgeEndpointUpper := by
    have hend := hbridge.2.2
    have hsum := partialSum_nextBlock_eq_blockSum
      (prefixLength := prefixLength) increment
      (Fin.last bridgeLength)
    have hlast : (Fin.last bridgeLength).val = bridgeLength := rfl
    rw [hsum, hlast] at hend
    exact hend
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
      simpa only [history_coordinate_eq_displacement] using hpoint'
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
      simpa only [history_coordinate_eq_displacement] using hpoint
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
    simpa only [history_coordinate_eq_displacement, Fin.val_last] using hendpoint

/-- The two finite blocks' probabilities multiply, and their intersection is
contained in the affine corridor event. -/
theorem iidSequenceLaw_measure_ge_mul_of_finiteMovingEntrance_downwardBridge
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
      {increment | Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈
        finiteCorridorBridgeEvent (n := bridgeLength)
          bridgeLower bridgeUpper bridgeEndpointLower bridgeEndpointUpper}) :
    entryMass * bridgeMass ≤ iidSequenceLaw ν
      {increment | RandomWalk.history horizon 0 increment ∈
        affineCorridorThrough horizon 0 drift width
          (drift * (horizon : ℝ) + terminalExtra)} := by
  let entrance : Set (Fin prefixLength → ℝ) :=
    finiteMovingEntranceEvent (n := prefixLength) entranceScale
      (drift / entranceScale) 0
  let bridge : Set (Fin bridgeLength → ℝ) :=
    finiteCorridorBridgeEvent (n := bridgeLength)
      bridgeLower bridgeUpper bridgeEndpointLower bridgeEndpointUpper
  let target : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history horizon 0 increment ∈
      affineCorridorThrough horizon 0 drift width
        (drift * (horizon : ℝ) + terminalExtra)}
  have hentranceMeasurable : MeasurableSet entrance := by
    have hsafe := measurableSet_finiteDriftRemovedOffsetCorridorEvent
      (n := prefixLength) entranceScale (drift / entranceScale) 0
    have hevent : finiteDriftRemovedOffsetCorridorEvent
        (n := prefixLength) entranceScale (drift / entranceScale) 0 = entrance := by
      ext block
      exact finiteDriftRemovedOffsetCorridorEvent_iff_finiteMovingEntranceEvent
        entranceScale (drift / entranceScale) 0 block
    rw [← hevent]
    exact hsafe
  have hbridgeMeasurable : MeasurableSet bridge :=
    measurableSet_finiteCorridorBridgeEvent
      bridgeLower bridgeUpper bridgeEndpointLower bridgeEndpointUpper
  have hfactor := RandomWalk.iidSequenceLaw_measure_inter_prefix_nextBlock
    ν prefixLength bridgeLength entrance bridge hentranceMeasurable hbridgeMeasurable
  have hsubset :
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ entrance ∧
          Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength
            increment ∈ bridge} ⊆ target := by
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
    _ ≤ iidSequenceLaw ν target := measure_mono hsubset
    _ = _ := rfl

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

end
