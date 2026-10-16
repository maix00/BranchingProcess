/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceUpper.Blocks
public import Probability.Process.Filtration.ConditionalBlocks

/-!
# Finite-variance upper bound for a tilted tube

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.exists_driftedTubeProbability_le_exp_of_finiteVariance`:
  for centered increments of variance $\sigma^2>0$, $v>0$, $c\ge0$,
  and $0<d<\pi^2\sigma^2/2$, sufficiently large widths satisfy
  $\mathbb P(T_{L,\Delta,c,r_0})\le
  \exp(\Delta^v-dL/\Delta^2)$ uniformly in $L\ge0$ and
  $-\Delta\le r_0\le0$.

This formalizes Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Chapter 3, Lemma 3.4. The proof follows the
equal-length block decomposition, conditional-expectation iteration, and
remainder estimate in that lemma. The block inputs are in
`FiniteVarianceUpper/Blocks.lean`.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

private theorem driftedTubeBlockPosition_eq
    (start length : ℕ) (increment : ℕ → ℝ)
    (k : Fin (length + 1)) :
    (∑ i : Fin start,
      Combinatorics.Sequence.blockCoordinates 0 start increment i) +
      Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates start length increment) k =
      AdditivePath.displacement (start + (k : ℕ)) increment := by
  have hprefix :
      (∑ i : Fin start,
        Combinatorics.Sequence.blockCoordinates 0 start increment i) =
        AdditivePath.displacement start increment := by
    simp [Combinatorics.Sequence.blockCoordinates, AdditivePath.displacement,
      Fin.sum_univ_eq_sum_range]
  calc
    _ = AdditivePath.displacement start increment +
        AdditivePath.blockSum start (k : ℕ) increment := by
      rw [hprefix, partialSum_blockCoordinates]
    _ = AdditivePath.displacement (start + (k : ℕ)) increment :=
      (AdditivePath.displacement_add_eq_add_blockSum start (k : ℕ)
        increment).symm

/-- The full small-drift upper estimate in Wang Yiyang, Chapter 3,
Lemma 3.4. The proof follows its equal-length block decomposition,
conditional-expectation iteration, and final-remainder estimate. -/
theorem exists_driftedTubeProbability_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance v drift d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance) (hv : 0 < v)
    (hdrift : 0 ≤ drift) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ lower : ℝ, -Delta ≤ lower → lower ≤ 0 →
      ∀ horizon : ℕ,
        (iidSequenceLaw ν).real
          (driftedTubeEvent horizon Delta drift lower) ≤
            Real.exp (Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2)) := by
  let eta : ℝ := min (v / 2) (1 / 2)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaV : eta < v := by
    dsimp [eta]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hetaOne : eta < 1 := by
    dsimp [eta]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hgrowth : ∀ᶠ Delta : ℝ in atTop, d ≤ Delta ^ (v - eta) :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < v - eta)).eventually
      (eventually_ge_atTop d)
  obtain ⟨DeltaBlock₀, hDeltaBlock₀, hblockProbability⟩ :=
    exists_driftedTubeBlockProbability_le_exp_of_finiteVariance
      ν hν hsquare hvariance hdrift heta hetaOne hd hcritical
  have hgood : ∀ᶠ Delta : ℝ in atTop,
      (1 ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
        Delta ^ (2 + eta) - Delta ^ (2 + eta / 2) ≤
          (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
        Delta ^ (2 + eta / 2) ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
        (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ≤ Delta ^ (2 + eta)) ∧
      d ≤ Delta ^ (v - eta) ∧ DeltaBlock₀ ≤ Delta ∧ 1 ≤ Delta := by
    filter_upwards
      [Drawdown.eventually_drawdownFloorBlockLength_bounds heta,
        hgrowth, eventually_ge_atTop DeltaBlock₀,
        eventually_ge_atTop (1 : ℝ)] with Delta hfloor hgrowthAt hblockWidth hDelta
    exact ⟨hfloor, hgrowthAt, hblockWidth, hDelta⟩
  obtain ⟨DeltaBound, hDeltaBound⟩ := Filter.eventually_atTop.1 hgood
  let Delta₀ := max 1 DeltaBound
  refine ⟨Delta₀, le_max_left _ _, ?_⟩
  intro Delta hDelta lower hlower hupper horizon
  have hDeltaLarge : DeltaBound ≤ Delta :=
    (le_max_right _ _).trans hDelta
  obtain ⟨hfloor, hgrowthAt, hblockWidth, hDeltaOne⟩ :=
    hDeltaBound Delta hDeltaLarge
  have hDeltaPos : 0 < Delta := by linarith
  let blockLength : ℕ := ⌊Delta ^ (2 + eta)⌋₊
  let q : ℕ := horizon / blockLength
  let p : ℝ := Real.exp (-d * ((blockLength : ℝ) / Delta ^ 2))
  have hblockLengthPos : 0 < blockLength := by
    have hpos : 1 ≤ (blockLength : ℝ) := by simpa [blockLength] using hfloor.1
    exact_mod_cast hpos
  have hblockLengthLower : Delta ^ (2 + eta / 2) ≤ (blockLength : ℝ) := by
    simpa [blockLength] using hfloor.2.2.1
  have hblockLengthUpper : (blockLength : ℝ) ≤ Delta ^ (2 + eta) := by
    simpa [blockLength] using hfloor.2.2.2
  have hDeltaPower : Delta ^ (2 + eta) = Delta ^ 2 * Delta ^ eta := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_add hDeltaPos 2 eta
  have hscaleGrowth : d * Delta ^ eta ≤ Delta ^ v := by
    calc
      d * Delta ^ eta = Delta ^ eta * d := by ring
      _ ≤ Delta ^ eta * Delta ^ (v - eta) :=
        mul_le_mul_of_nonneg_left hgrowthAt (by positivity)
      _ = Delta ^ v := by
        rw [← Real.rpow_add hDeltaPos]
        congr 1
        ring
  by_cases hshort : horizon < blockLength
  · have hhorizonScale :
        (horizon : ℝ) / Delta ^ 2 ≤ Delta ^ eta := by
      apply (div_le_iff₀ (sq_pos_of_pos hDeltaPos)).2
      calc
        (horizon : ℝ) ≤ (blockLength : ℝ) := by exact_mod_cast hshort.le
        _ ≤ Delta ^ (2 + eta) := hblockLengthUpper
        _ = Delta ^ 2 * Delta ^ eta := hDeltaPower
        _ = Delta ^ eta * Delta ^ 2 := by ring
    have hbudget : d * ((horizon : ℝ) / Delta ^ 2) ≤ Delta ^ v :=
      (mul_le_mul_of_nonneg_left hhorizonScale hd.le).trans hscaleGrowth
    have hexponent : 0 ≤ Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2) := by
      linarith
    have hprobability : (iidSequenceLaw ν).real
        (driftedTubeEvent horizon Delta drift lower) ≤ 1 := by
      calc
        _ ≤ (iidSequenceLaw ν).real Set.univ :=
          measureReal_mono (Set.subset_univ _) (measure_ne_top (iidSequenceLaw ν) _)
        _ = 1 := by simp
    exact hprobability.trans (Real.one_le_exp_iff.mpr hexponent)
  · have hblockRate : ∀ localLower : ℝ, -Delta ≤ localLower →
        localLower ≤ 0 →
        (iidSequenceLaw ν).real
          (driftedTubeEvent blockLength Delta drift localLower) ≤ p := by
      intro localLower hlocalLower hlocalUpper
      have h := hblockProbability Delta hblockWidth localLower
        hlocalLower hlocalUpper
      simpa [p] using h
    let events : ℕ → Set (ℕ → ℝ) := fun j =>
      driftedTubeBlockEvent (j * blockLength) blockLength lower Delta drift
    let filtration : ℕ → MeasurableSpace (ℕ → ℝ) := fun j =>
      ProbabilityTheory.sequencePrefixFiltration (E := ℝ) (j * blockLength)
    have hfiltrationMono : ∀ j, filtration j ≤ filtration (j + 1) := by
      intro j
      dsimp [filtration]
      apply (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).mono'
      have htime : j * blockLength + blockLength = (j + 1) * blockLength := by
        simp [Nat.succ_mul]
      rw [← htime]
      exact Nat.le_add_right _ _
    have hfiltrationAmbient : ∀ j,
        filtration j ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
      intro j
      exact (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).le'
        (j * blockLength)
    have heventMeasurable : ∀ j,
        MeasurableSet[filtration (j + 1)] (events j) := by
      intro j
      have htime : (j + 1) * blockLength =
          j * blockLength + blockLength := by
        rw [Nat.add_mul, one_mul]
      change MeasurableSet[ProbabilityTheory.sequencePrefixFiltration
        (E := ℝ) ((j + 1) * blockLength)]
        (driftedTubeBlockEvent (j * blockLength) blockLength
          lower Delta drift)
      rw [htime]
      exact measurableSet_driftedTubeBlockEvent
        (j * blockLength) blockLength lower Delta drift
    have hconditional : ∀ j, ∀ᵐ increment ∂iidSequenceLaw ν,
        condExp (filtration j) (iidSequenceLaw ν)
          ((events j).indicator (fun _ => (1 : ℝ))) increment ≤ p := by
      intro j
      have h := iidSequenceLaw_condExp_driftedTubeBlockEvent_le_of_blockBound
        (lower := lower) (width := Delta) (drift := drift) (bound := p)
        ν (j * blockLength) blockLength (by positivity) hblockRate
      filter_upwards [h] with increment hbound
      simpa [filtration, events] using hbound
    have hconditionalOnPrefix : ∀ j, ∀ᵐ increment ∂iidSequenceLaw ν,
        increment ∈ ProbabilityTheory.conditionalBlockIntersection events j →
          condExp (filtration j) (iidSequenceLaw ν)
            ((events j).indicator (fun _ => (1 : ℝ))) increment ≤ p := by
      intro j
      filter_upwards [hconditional j] with increment hbound
      intro _
      exact hbound
    have hprobabilityBlocks :
        (iidSequenceLaw ν).real
          (ProbabilityTheory.conditionalBlockIntersection events q) ≤ p ^ q :=
      ProbabilityTheory.measureReal_conditionalBlockIntersection_le_pow
        filtration hfiltrationMono hfiltrationAmbient events heventMeasurable
        (Real.exp_nonneg _) hconditionalOnPrefix q
    have hblockPath (increment : ℕ → ℝ) (hpath :
        increment ∈ driftedTubeEvent horizon Delta drift lower) :
        ∀ j < q, increment ∈ events j := by
      intro j hj
      have hblockTime : (j + 1) * blockLength ≤ q * blockLength :=
        Nat.mul_le_mul_right blockLength (Nat.succ_le_of_lt hj)
      have hcount : q * blockLength ≤ horizon := by
        dsimp [q]
        exact Nat.div_mul_le_self _ _
      change ∀ k : Fin (blockLength + 1),
        lower + drift *
            ((j * blockLength + (k : ℕ) : ℕ) : ℝ) / Delta ^ 2 ≤
          (∑ i : Fin (j * blockLength),
            Combinatorics.Sequence.blockCoordinates 0 (j * blockLength) increment i) +
            Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates (j * blockLength)
                blockLength increment) k ∧
        (∑ i : Fin (j * blockLength),
            Combinatorics.Sequence.blockCoordinates 0 (j * blockLength) increment i) +
            Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates (j * blockLength)
                blockLength increment) k ≤
          lower + drift *
            ((j * blockLength + (k : ℕ) : ℕ) : ℝ) / Delta ^ 2 + Delta
      intro k
      have hposition := driftedTubeBlockPosition_eq
        (j * blockLength) blockLength increment k
      have hk : (k : ℕ) ≤ blockLength := Nat.le_of_lt_succ k.isLt
      have htime : j * blockLength + (k : ℕ) ≤ horizon := by
        calc
          j * blockLength + (k : ℕ) ≤ j * blockLength + blockLength :=
            Nat.add_le_add_left hk _
          _ = (j + 1) * blockLength := by simp [Nat.succ_mul]
          _ ≤ q * blockLength := hblockTime
          _ ≤ horizon := hcount
      by_cases htimeZero : j * blockLength + (k : ℕ) = 0
      · have htimeCast :
            ((j * blockLength + (k : ℕ) : ℕ) : ℝ) = 0 := by
          exact_mod_cast htimeZero
        have hpositionZero :
            (∑ i : Fin (j * blockLength),
              Combinatorics.Sequence.blockCoordinates 0 (j * blockLength)
                increment i) +
              Fin.partialSum
                (Combinatorics.Sequence.blockCoordinates (j * blockLength)
                  blockLength increment) k = 0 := by
          rw [hposition, htimeZero, AdditivePath.displacement_zero]
        constructor
        · rw [hpositionZero, htimeCast]
          simp only [mul_zero, zero_div, add_zero]
          linarith [hlower]
        · rw [hpositionZero, htimeCast]
          simp only [mul_zero, zero_div, add_zero]
          linarith [hupper]
      · have hpathAt := hpath (j * blockLength + (k : ℕ))
          (Nat.one_le_iff_ne_zero.mpr htimeZero) htime
        rw [← hposition] at hpathAt
        exact hpathAt
    have hsubset : driftedTubeEvent horizon Delta drift lower ⊆
        ProbabilityTheory.conditionalBlockIntersection events q := by
      intro increment hpath
      have hmembers : ∀ n ≤ q,
          increment ∈ ProbabilityTheory.conditionalBlockIntersection events n := by
        intro n
        induction n with
        | zero =>
            intro _
            simp [ProbabilityTheory.conditionalBlockIntersection]
        | succ n ih =>
            intro hn
            rw [ProbabilityTheory.conditionalBlockIntersection]
            exact ⟨ih (by omega), hblockPath increment hpath n (by omega)⟩
      exact hmembers q le_rfl
    have hprobability :
        (iidSequenceLaw ν).real (driftedTubeEvent horizon Delta drift lower) ≤
          (iidSequenceLaw ν).real
            (ProbabilityTheory.conditionalBlockIntersection events q) :=
      measureReal_mono hsubset (measure_ne_top (iidSequenceLaw ν) _)
    have hdivision : q * blockLength + horizon % blockLength = horizon := by
      dsimp [q]
      rw [Nat.mul_comm (horizon / blockLength) blockLength, Nat.add_comm]
      exact Nat.mod_add_div horizon blockLength
    have hremainder : horizon % blockLength < blockLength :=
      Nat.mod_lt _ hblockLengthPos
    have hremainderFraction :
        ((horizon % blockLength : ℕ) : ℝ) / Delta ^ 2 ≤ Delta ^ eta := by
      apply (div_le_iff₀ (sq_pos_of_pos hDeltaPos)).2
      calc
        ((horizon % blockLength : ℕ) : ℝ) ≤ (blockLength : ℝ) := by
          exact_mod_cast hremainder.le
        _ ≤ Delta ^ (2 + eta) := hblockLengthUpper
        _ = Delta ^ 2 * Delta ^ eta := hDeltaPower
        _ = Delta ^ eta * Delta ^ 2 := by ring
    have hremainderCost :
        d * (((horizon % blockLength : ℕ) : ℝ) / Delta ^ 2) ≤ Delta ^ v := by
      calc
        _ ≤ d * Delta ^ eta :=
          mul_le_mul_of_nonneg_left hremainderFraction hd.le
        _ = Delta ^ eta * d := by ring
        _ ≤ Delta ^ eta * Delta ^ (v - eta) :=
          mul_le_mul_of_nonneg_left hgrowthAt (by positivity)
        _ = Delta ^ v := by
          rw [← Real.rpow_add hDeltaPos]
          congr 1
          ring
    have hdivisionReal :
        ((q * blockLength : ℕ) : ℝ) +
            ((horizon % blockLength : ℕ) : ℝ) = (horizon : ℝ) := by
      exact_mod_cast hdivision
    have hexponent :
        -d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2) ≤
          Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2) := by
      rw [show ((q * blockLength : ℕ) : ℝ) =
        (horizon : ℝ) - ((horizon % blockLength : ℕ) : ℝ) by linarith]
      have hidentity :
          -d * (((horizon : ℝ) - ((horizon % blockLength : ℕ) : ℝ)) /
              Delta ^ 2) =
            -d * ((horizon : ℝ) / Delta ^ 2) +
              d * (((horizon % blockLength : ℕ) : ℝ) / Delta ^ 2) := by
        ring
      rw [hidentity]
      linarith [hremainderCost]
    have hpower : p ^ q = Real.exp
        (-d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2)) := by
      calc
        p ^ q = Real.exp
            ((-d * ((blockLength : ℝ) / Delta ^ 2)) * (q : ℝ)) := by
          dsimp [p]
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        _ = Real.exp (-d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2)) := by
          congr 1
          push_cast
          ring
    calc
      (iidSequenceLaw ν).real (driftedTubeEvent horizon Delta drift lower) ≤
          (iidSequenceLaw ν).real
            (ProbabilityTheory.conditionalBlockIntersection events q) := hprobability
      _ ≤ p ^ q := hprobabilityBlocks
      _ = Real.exp (-d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2)) := hpower
      _ ≤ Real.exp (Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2)) :=
        Real.exp_le_exp.mpr hexponent

end ProbabilityTheory.RandomWalk.SmallDeviation

end
