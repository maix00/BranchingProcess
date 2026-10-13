/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RightTailSecondStageBridge
import Probability.Process.RandomWalk.SmallDeviation.Entrance.FiniteVarianceEndpointCorridor

/-!
# Finite-variance probability for a restarted affine corridor

The entrance block follows the affine lower boundary. A later block follows
a fixed downward corridor. Finite variance supplies lower bounds for both
blocks, and the deterministic splice puts their intersection in the full
affine corridor.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
open ProbabilityTheory.BranchingRandomWalk.Spine

private theorem history_coordinate_eq_displacement (n : ℕ)
    (increment : ℕ → ℝ) (i : Fin (n + 1)) :
    RandomWalk.history n 0 increment i = AdditivePath.displacement i.val increment := by
  rw [RandomWalk.history_eq_fromIncrements]
  simp [AdditivePath.fromIncrements, AdditivePath.displacement]

private theorem partialSum_prefixBlock_eq_displacement
    {prefixLength : ℕ} (increment : ℕ → ℝ)
    (j : Fin (prefixLength + 1)) :
    Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j =
      AdditivePath.displacement j.val increment := by
  rw [RandomWalk.partialSum_blockCoordinates,
    AdditivePath.blockSum_eq_displacement_natAdd]
  simp

private theorem history_eq_partialSum_prefixBlock
    {n : ℕ} (increment : ℕ → ℝ) (j : Fin (n + 1)) :
    RandomWalk.history n 0 increment j =
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates 0 n increment) j := by
  rw [history_coordinate_eq_displacement, ← partialSum_prefixBlock_eq_displacement]

private theorem endpointCorridorEvent_subset_finiteCorridorBridgeEvent
    (n : ℕ) (D : ℝ) :
    {increment : ℕ → ℝ |
      InClosedInterval (-2 * D) 0 n 0 increment ∧
        AdditivePath.displacement n increment ∈ Set.Icc (-2 * D) (-D)} ⊆
    {increment : ℕ → ℝ |
      Combinatorics.Sequence.blockCoordinates 0 n increment ∈
        finiteCorridorBridgeEvent (n := n) (-2 * D) 0 (-2 * D) (-D)} := by
  intro increment h
  have hpath : ∀ j : Fin (n + 1),
      RandomWalk.history n 0 increment j ∈ Set.Icc (-2 * D) 0 := by
    simpa [InClosedInterval, InWindows] using h.1
  refine ⟨?_, ?_⟩
  · intro j
    rw [← history_eq_partialSum_prefixBlock increment j]
    exact hpath j
  · have hlast := partialSum_prefixBlock_eq_displacement increment (Fin.last n)
    have hval : (Fin.last n).val = n := rfl
    simpa only [hlast, hval] using h.2

/-- For every sufficiently long bridge, the finite-variance endpoint-corridor
bound also bounds the finite block event used by the affine splice. -/
theorem exists_eventually_iidSequenceLaw_finiteCorridorBridgeEvent_lowerBound_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {bridgeScale : ℕ → ℝ} (hbridgeScale : IsMogulskiiScale bridgeScale) :
    ∃ C : ℝ, C < 0 ∧ ∃ q : ℝ≥0∞, 0 < q ∧
      ∃ amplitude : ℝ, 0 < amplitude ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ENNReal.ofReal (Real.exp
          ((C / ((2 / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
            (Asymptotics.balancedBlockCount
              (finiteVarianceBridgeLength bridgeScale n -
                stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale n)
              (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale n) + 1) *
            (q / (finiteVarianceEntranceLength bridgeScale n : ℝ≥0∞)) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              Combinatorics.Sequence.blockCoordinates 0 n increment ∈
                finiteCorridorBridgeEvent (n := n)
                  (-2 * bridgeScale n) 0 (-2 * bridgeScale n) (-bridgeScale n)} := by
  obtain ⟨C, hC, q, hq, amplitude, hamplitude, n₀, hbound⟩ :=
    exists_eventually_iidSequenceLaw_endpointCorridor_lowerBound_of_centeredSecondMoment
      hν hsigma hbridgeScale (2 : ℝ) (by norm_num)
  refine ⟨C, hC, q, hq, amplitude, hamplitude, n₀, ?_⟩
  intro n hn
  have hsubset := endpointCorridorEvent_subset_finiteCorridorBridgeEvent
    n (bridgeScale n)
  have hsource := hbound n hn
  have hsource' :
      ENNReal.ofReal (Real.exp
          ((C / ((2 / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
            (Asymptotics.balancedBlockCount
              (finiteVarianceBridgeLength bridgeScale n -
                stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale n)
              (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale n) + 1) *
            (q / (finiteVarianceEntranceLength bridgeScale n : ℝ≥0∞)) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              InClosedInterval (-2 * bridgeScale n) 0 n 0 increment ∧
                AdditivePath.displacement n increment ∈
                  Set.Icc (-2 * bridgeScale n) (-bridgeScale n)} := by
    simpa only [show ((-(2 : ℝ) + 1) * bridgeScale n) = -bridgeScale n by ring]
      using hsource
  exact hsource'.trans (measure_mono hsubset)

/-- A centered finite-second-moment increment law gives an explicit eventual
lower bound for the positive-drift affine corridor. The only probability
input is the centered second moment; the remaining hypotheses describe the
deterministic scales and the four margins needed to splice the two blocks. -/
theorem eventually_iidSequenceLaw_affineCorridorThrough_lowerBound_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (horizon : ℕ → ℕ) (entranceScale drift width terminalExtra : ℕ → ℝ)
    (bridgeScale : ℕ → ℝ) (entryDrift : ℝ)
    (hentryDrift : 0 ≤ entryDrift)
    (hentranceScale : Tendsto entranceScale atTop atTop)
    (hbridgeScale : IsMogulskiiScale bridgeScale)
    (hbridgeLength : Tendsto
      (fun n => ((horizon n - ⌊entranceScale n ^ 2⌋₊ : ℕ) : ℝ)) atTop atTop)
    (hdrift : ∀ n, drift n = entryDrift / entranceScale n ^ 2)
    (hprefixLe : ∀ᶠ n : ℕ in atTop, ⌊entranceScale n ^ 2⌋₊ ≤ horizon n)
    (hentranceWidth : ∀ᶠ n : ℕ in atTop, entranceScale n ≤ width n)
    (hbridgeLower : ∀ᶠ n : ℕ in atTop,
      entranceScale n / 3 - 2 * bridgeScale
          (horizon n - ⌊entranceScale n ^ 2⌋₊) ≥
        drift n * ((horizon n - ⌊entranceScale n ^ 2⌋₊ : ℕ) : ℝ))
    (hbridgeUpper : ∀ᶠ n : ℕ in atTop,
      2 * entranceScale n / 3 ≤ width n)
    (hterminal : ∀ᶠ n : ℕ in atTop,
      2 * entranceScale n / 3 - bridgeScale
          (horizon n - ⌊entranceScale n ^ 2⌋₊) ≤
        drift n * ((horizon n - ⌊entranceScale n ^ 2⌋₊ : ℕ) : ℝ) +
          terminalExtra n) :
    ∃ entryMass : ℝ≥0∞, 0 < entryMass ∧
      ∃ C : ℝ, C < 0 ∧ ∃ bridgeQ : ℝ≥0∞, 0 < bridgeQ ∧
        ∃ amplitude : ℝ, 0 < amplitude ∧
          ∀ᶠ n : ℕ in atTop,
            entryMass / (⌊entranceScale n ^ 2⌋₊ : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp
                ((C / ((2 / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
                (Asymptotics.balancedBlockCount
                  (finiteVarianceBridgeLength bridgeScale
                      (horizon n - ⌊entranceScale n ^ 2⌋₊) -
                    stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale
                      (horizon n - ⌊entranceScale n ^ 2⌋₊))
                  (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale
                    (horizon n - ⌊entranceScale n ^ 2⌋₊)) + 1)) *
                (bridgeQ /
                  (finiteVarianceEntranceLength bridgeScale
                    (horizon n - ⌊entranceScale n ^ 2⌋₊) : ℝ≥0∞)) ≤
              iidSequenceLaw ν
                {increment : ℕ → ℝ |
                  RandomWalk.history (horizon n) 0 increment ∈
                    affineCorridorThrough (horizon n) 0 (drift n) (width n)
                      (drift n * (horizon n : ℝ) + terminalExtra n)} := by
  obtain ⟨entryQ, hentryQ, entryDelta, hentry⟩ :=
    exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment
      hν hsigma entryDrift hentryDrift
  obtain ⟨C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude,
      bridgeDelta, hbridgeMass⟩ :=
    exists_eventually_iidSequenceLaw_finiteCorridorBridgeEvent_lowerBound_of_centeredSecondMoment
      hν hsigma hbridgeScale
  have hentryEventually : ∀ᶠ n : ℕ in atTop, entryDelta ≤ entranceScale n :=
    hentranceScale.eventually_ge_atTop entryDelta
  have hbridgeLengthEventually : ∀ᶠ n : ℕ in atTop,
      bridgeDelta ≤ horizon n - ⌊entranceScale n ^ 2⌋₊ := by
    have h := hbridgeLength.eventually_ge_atTop bridgeDelta
    exact h.mono fun n hn => by exact_mod_cast hn
  have hentrancePositive : ∀ᶠ n : ℕ in atTop, 0 < entranceScale n :=
    hentranceScale.eventually_gt_atTop 0
  refine ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude, ?_⟩
  filter_upwards [hentryEventually, hbridgeLengthEventually, hentrancePositive,
    hprefixLe, hentranceWidth, hbridgeLower, hbridgeUpper, hterminal,
    hentranceScale.eventually_gt_atTop 0] with n hentryDelta hbridgeDelta
      hEpos hprefix hwidth hlow hup hterm hEpos'
  let prefixLength := ⌊entranceScale n ^ 2⌋₊
  let bridgeLength := horizon n - prefixLength
  have hpartition : prefixLength + bridgeLength = horizon n := by
    dsimp [prefixLength, bridgeLength]
    omega
  have hcoeff : entryDrift / entranceScale n ^ 3 = drift n / entranceScale n := by
    rw [hdrift n]
    field_simp [ne_of_gt hEpos]
  have hentryMass : entryQ / (prefixLength : ℝ≥0∞) ≤
      iidSequenceLaw ν
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
            finiteMovingEntranceEvent (n := prefixLength) (entranceScale n)
              (drift n / entranceScale n) 0} := by
    have h := hentry (entranceScale n) hentryDelta 0
      (by simp [Set.mem_Icc, hEpos.le])
    have hset :
        {increment : ℕ → ℝ |
          finitePrefixVector (n := prefixLength) increment ∈
            finiteMovingEntranceEvent (n := prefixLength) (entranceScale n)
              (entryDrift / (entranceScale n) ^ 3) 0} =
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
            finiteMovingEntranceEvent (n := prefixLength) (entranceScale n)
              (drift n / entranceScale n) 0} := by
      ext increment
      simp only [Set.mem_ofPred_eq]
      have hvec :
          finitePrefixVector (n := prefixLength) increment =
            Combinatorics.Sequence.blockCoordinates 0 prefixLength increment := by
        funext i
        simp [finitePrefixVector, Combinatorics.Sequence.blockCoordinates]
      change finitePrefixVector (n := prefixLength) increment ∈
          finiteMovingEntranceEvent (entranceScale n)
            (entryDrift / entranceScale n ^ 3) 0 ↔
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
          finiteMovingEntranceEvent (entranceScale n)
            (drift n / entranceScale n) 0
      rw [hvec, hcoeff]
    have hentryZero : entryQ / (prefixLength : ℝ≥0∞) ≤
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            finitePrefixVector (n := prefixLength) increment ∈
              finiteMovingEntranceEvent (n := prefixLength) (entranceScale n)
                (entryDrift / (entranceScale n) ^ 3) 0} := by
      simpa using h
    calc
      entryQ / (prefixLength : ℝ≥0∞) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              finitePrefixVector (n := prefixLength) increment ∈
                finiteMovingEntranceEvent (n := prefixLength) (entranceScale n)
                  (entryDrift / (entranceScale n) ^ 3) 0} := hentryZero
      _ = iidSequenceLaw ν
          {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
              finiteMovingEntranceEvent (n := prefixLength) (entranceScale n)
                (drift n / entranceScale n) 0} := by rw [hset]
      _ = _ := by simp [prefixLength]
  let bridgeMass : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp
      ((C / ((2 / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
        (Asymptotics.balancedBlockCount
          (finiteVarianceBridgeLength bridgeScale bridgeLength -
            stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale bridgeLength)
          (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) bridgeScale bridgeLength) + 1) *
        (bridgeQ / (finiteVarianceEntranceLength bridgeScale bridgeLength : ℝ≥0∞))
  have hbridgeMass' : bridgeMass ≤
      iidSequenceLaw ν
        {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈
            finiteCorridorBridgeEvent (n := bridgeLength)
              (-2 * bridgeScale bridgeLength) 0 (-2 * bridgeScale bridgeLength)
              (-bridgeScale bridgeLength)} := by
    dsimp [bridgeMass]
    exact hbridgeMass bridgeLength hbridgeDelta
  have hlow' : entranceScale n / 3 + -2 * bridgeScale bridgeLength ≥
      drift n * (bridgeLength : ℝ) := by
    rw [show bridgeLength = horizon n - ⌊entranceScale n ^ 2⌋₊ by rfl]
    linarith [hlow]
  have hup' : 2 * entranceScale n / 3 + (0 : ℝ) ≤ width n := by
    linarith [hup]
  have hterm' : 2 * entranceScale n / 3 + -bridgeScale bridgeLength ≤
      drift n * (bridgeLength : ℝ) + terminalExtra n := by
    rw [show bridgeLength = horizon n - ⌊entranceScale n ^ 2⌋₊ by rfl]
    linarith [hterm]
  have hdrift0 : 0 ≤ drift n := by
    rw [hdrift n]
    positivity
  have hspine := iidSequenceLaw_measure_ge_mul_of_finiteMovingEntrance_downwardBridge
    (ν := ν)
    (horizon n) prefixLength bridgeLength hpartition
    (entranceScale n) (drift n) (width n) (terminalExtra n)
    (-2 * bridgeScale bridgeLength) 0 (-2 * bridgeScale bridgeLength)
    (-bridgeScale bridgeLength)
    hEpos hdrift0 hwidth hlow' hup' hterm'
    (entryQ / (prefixLength : ℝ≥0∞)) bridgeMass hentryMass hbridgeMass'
  have hevent :
      {increment : ℕ → ℝ |
        RandomWalk.history (horizon n) 0 increment ∈
          affineCorridorThrough (horizon n) 0 (drift n) (width n)
            (drift n * (horizon n : ℝ) + terminalExtra n)} =
      {increment : ℕ → ℝ |
        (fun k => AdditivePath.displacement k.val increment) ∈
          affineCorridorThrough (horizon n) 0 (drift n) (width n)
            (drift n * (horizon n : ℝ) + terminalExtra n)} := by
    ext increment
    simp only [Set.mem_ofPred_eq]
    have hpath : RandomWalk.history (horizon n) 0 increment =
        (fun k => AdditivePath.displacement k.val increment) := by
      funext k
      exact history_coordinate_eq_displacement (horizon n) increment k
    rw [hpath]
  rw [hevent]
  rw [← mul_assoc] at hspine
  simpa [prefixLength, bridgeLength, bridgeMass] using hspine

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
