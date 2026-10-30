/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Sequence.IID.Blocks.FiniteCover
import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomain
import Probability.Process.RandomWalk.Path.Block.Corridor.CoreReturn
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.FinitePath
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Endpoint.BandTransfer.Lower.CellBridge
/-!
# Proof support for the finite-variance endpoint corridor

Let $E_n$ be the finite entrance event and $B_n$ the endpoint-core bridge event.

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.FiniteVariance.Lemmas.iidSequenceLaw_measure_mul_of_finiteMovingEntranceEvent_bridge`:
  if $q\leq\mathbb P(E_n)$ and $p\leq\mathbb P(B_n)$, then
  $pq\leq\mathbb P(\text{the concatenated path stays in }[-rD,0]
  \text{ and ends in }[-rD,(1-r)D])$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.FiniteVariance.Lemmas.exists_eventually_iidSequenceLaw_rightEndpointBridge_ge_stableCellLowerBound`:
  under the stable index-two path-limit and escape-rate assumptions, for
  every $r>1$ there are $a>0$ and an eventual lower bound
  $\exp\!([C/(r/2-13/60)^2-1]a^2)^{k_n}\leq\mathbb P(B_n)$, with
  $k_n=\operatorname{balancedBlockCount}(N_n-\ell_n,\ell_n)+1$ and
  $\ell_n=\operatorname{stableBlockLength}(2,\nu,a^2,\mathrm{scale},n)$.

These two event-specific steps support the finite-variance corridor estimate.
The endpoint-core product follows A. A. Mogul'skii, Theorem 3, Section 4,
p. 764, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. The concatenation
is used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (master's thesis, Fudan University, 2026), Appendix A.2,
Lemma A.7, in the proof of Chapter 3, Lemma 3.5.
-/

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.FiniteVariance.Lemmas

open ProbabilityTheory.RandomWalk.SmallDeviation.Entrance
open ProbabilityTheory.RandomWalk

/-- An entrance block of width `D`, followed by a robust endpoint-core block,
produces a path that stays in `[-ratio * D, 0]` and ends in the final interval
`[-ratio * D, (-ratio + 1) * D]`.  The source core is the central third of the
entrance corridor. -/
lemma iidSequenceLaw_measure_mul_of_finiteMovingEntranceEvent_bridge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (prefixLength bridgeLength : ℕ) (D ratio : ℝ)
    (hD : 0 < D) (hratio : 1 < ratio)
    (entryLower bridgeLower : ℝ≥0∞)
    (hentry : entryLower ≤ iidSequenceLaw ν
      {increment : ℕ → ℝ |
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength) increment ∈
          finiteMovingEntranceEvent (n := prefixLength) D 0 1})
    (hbridge : bridgeLower ≤ iidSequenceLaw ν
      {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈
          {block : Fin bridgeLength → ℝ |
            InOpenPartialSumCoreReturn
              (-ratio * D) 0 (-D / 2) (D / 6)
              ((-ratio + 1 / 2) * D) (D / 2) block}}) :
    bridgeLower * entryLower ≤ iidSequenceLaw ν
      {increment : ℕ → ℝ |
        InClosedInterval (-ratio * D) 0 (prefixLength + bridgeLength) 0 increment ∧
        AdditivePath.displacement (prefixLength + bridgeLength) increment ∈
          Set.Icc (-ratio * D) ((-ratio + 1) * D)} := by
  classical
  let entrance : Set (Fin prefixLength → ℝ) :=
    finiteMovingEntranceEvent (n := prefixLength) D 0 1
  let bridge : Set (Fin bridgeLength → ℝ) :=
    {block | InOpenPartialSumCoreReturn
      (-ratio * D) 0 (-D / 2) (D / 6)
      ((-ratio + 1 / 2) * D) (D / 2) block}
  let entranceSequence : Set (ℕ → ℝ) :=
    {increment | Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
      entrance}
  let target : Set (ℕ → ℝ) :=
    {increment |
      InClosedInterval (-ratio * D) 0 (prefixLength + bridgeLength) 0 increment ∧
      AdditivePath.displacement (prefixLength + bridgeLength) increment ∈
        Set.Icc (-ratio * D) ((-ratio + 1) * D)}
  have hentranceMeasurable : MeasurableSet entrance := by
    simpa [entrance] using measurableSet_finiteMovingEntranceEvent
      (n := prefixLength) D 0 1
  have hbridgeMeasurable : MeasurableSet bridge :=
    measurableSet_inOpenPartialSumCoreReturn
      (-ratio * D) 0 (-D / 2) (D / 6)
      ((-ratio + 1 / 2) * D) (D / 2)
  have hentrySequence : entryLower ≤ iidSequenceLaw ν entranceSequence := by
    have hset : entranceSequence =
        {increment : ℕ → ℝ |
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength) increment ∈ entrance} := by
      ext increment
      change Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ entrance ↔
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength) increment ∈ entrance
      rfl
    rw [hset]
    simpa [entrance] using hentry
  have hbridgeGeometry (increment : ℕ → ℝ)
      (hfirst : Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈
        entrance)
      (hnext : Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength
        increment ∈ bridge) : increment ∈ target := by
    have hfirstSpec :=
      (mem_finiteMovingEntranceEvent_iff D 0 1
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)).mp hfirst
    have hfirstPath (j : Fin (prefixLength + 1)) :
        AdditivePath.displacement j.val increment ∈ Set.Icc (-D) 0 := by
      have hsum : Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j =
          AdditivePath.displacement j.val increment := by
        rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
      have hraw : finiteNormalizedStepKnots D
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment) j ∈
            Set.Icc (-1) 0 := by
        simpa [finiteNormalizedStepKnots] using hfirstSpec.1 j
      rw [finiteNormalizedStepKnots, hsum] at hraw
      rcases Set.mem_Icc.mp hraw with ⟨hlo, hhi⟩
      have hmul : D * (D⁻¹ * AdditivePath.displacement j.val increment) =
          AdditivePath.displacement j.val increment := by
        field_simp [hD.ne']
      constructor
      · have := mul_le_mul_of_nonneg_left hlo hD.le
        rw [hmul] at this
        nlinarith
      · have := mul_le_mul_of_nonneg_left hhi hD.le
        rw [hmul] at this
        nlinarith
    have hendpointRaw :
        finiteNormalizedStepKnots D
          (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
          (Fin.last prefixLength) ∈ Set.Icc (-(2 / 3 : ℝ)) (-(1 / 3 : ℝ)) := by
      have hend := hfirstSpec.2
      change (1 / 3 - 1 + 0 * (prefixLength : ℝ) ≤
          finiteNormalizedStepKnots D
            (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
            (Fin.last prefixLength)) ∧
        finiteNormalizedStepKnots D
            (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
            (Fin.last prefixLength) ≤ 2 / 3 - 1 + 0 * (prefixLength : ℝ) at hend
      rcases hend with ⟨hlo, hhi⟩
      constructor <;> nlinarith
    have hsumLast : Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 prefixLength increment)
        (Fin.last prefixLength) = AdditivePath.displacement prefixLength increment := by
      simpa [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    rw [finiteNormalizedStepKnots, hsumLast] at hendpointRaw
    have hendpoint : AdditivePath.displacement prefixLength increment ∈
        Set.Icc (-2 * D / 3) (-D / 3) := by
      rcases Set.mem_Icc.mp hendpointRaw with ⟨hlo, hhi⟩
      have hmul : D * (D⁻¹ * AdditivePath.displacement prefixLength increment) =
          AdditivePath.displacement prefixLength increment := by
        field_simp [hD.ne']
      constructor
      · have := mul_le_mul_of_nonneg_left hlo hD.le
        rw [hmul] at this
        nlinarith
      · have := mul_le_mul_of_nonneg_left hhi hD.le
        rw [hmul] at this
        nlinarith
    have hsourceCore : AdditivePath.displacement prefixLength increment ∈
        Set.Icc ((-D / 2) - D / 6) ((-D / 2) + D / 6) := by
      rcases hendpoint with ⟨hlo, hhi⟩
      constructor <;> nlinarith
    have hblock : InOpenPartialSumCoreReturn
        (-ratio * D) 0 (-D / 2) (D / 6)
        ((-ratio + 1 / 2) * D) (D / 2)
        (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) :=
      hnext
    have hpositions := inOpenPartialSumCoreReturn_positions_mem
      (x := AdditivePath.displacement prefixLength increment)
      hsourceCore hblock
    have hpartial (j : Fin (bridgeLength + 1)) :
        Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) j =
          AdditivePath.blockSum prefixLength j.val increment := by
      simp [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
    have hglobal (j : Fin (bridgeLength + 1)) :
        AdditivePath.displacement (prefixLength + j.val) increment =
          AdditivePath.displacement prefixLength increment +
            Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment) j := by
      rw [AdditivePath.displacement_add_eq_add_blockSum, hpartial]
    have hpath : InClosedInterval (-ratio * D) 0
        (prefixLength + bridgeLength) 0 increment := by
      change ∀ k : Fin (prefixLength + bridgeLength + 1),
        history (prefixLength + bridgeLength) 0 increment k ∈
          Set.Icc (-ratio * D) 0
      intro k
      rw [history_eq_fromIncrements]
      simp only [AdditivePath.fromIncrements, zero_add]
      by_cases hk : k.val ≤ prefixLength
      · let j : Fin (prefixLength + 1) := ⟨k.val, by omega⟩
        have hj := hfirstPath j
        have hlower : -ratio * D ≤ -D := by nlinarith [hratio, hD]
        have hjval : j.val = k.val := by simp [j]
        rw [hjval] at hj
        have hj' : AdditivePath.displacement k.val increment ∈ Set.Icc (-D) 0 := by
          exact hj
        exact ⟨hlower.trans hj'.1, hj'.2⟩
      · let j : Fin (bridgeLength + 1) :=
          ⟨k.val - prefixLength, by omega⟩
        have hindex : k.val = prefixLength + j.val := by
          dsimp [j]
          omega
        rw [hindex, hglobal j]
        have hpos := hpositions j
        rcases hpos with ⟨hlo, hhi⟩
        constructor
        · exact le_of_lt hlo
        · exact le_of_lt hhi
    have hradius : D / 6 < D / 2 := by linarith
    have hendCore := inOpenPartialSumCoreReturn_endpoint_mem
      (x := AdditivePath.displacement prefixLength increment)
      hradius hsourceCore hblock
    have hlast : AdditivePath.displacement (prefixLength + bridgeLength) increment =
        AdditivePath.displacement prefixLength increment +
          Fin.partialSum
            (Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment)
            (Fin.last bridgeLength) := by
      simpa using hglobal (Fin.last bridgeLength)
    rw [← hlast] at hendCore
    have hend : AdditivePath.displacement (prefixLength + bridgeLength) increment ∈
        Set.Icc (-ratio * D) ((-ratio + 1) * D) := by
      rcases hendCore with ⟨hlo, hhi⟩
      constructor
      · have heq : (-ratio + 1 / 2) * D - D / 2 = -ratio * D := by ring
        rw [heq] at hlo
        exact le_of_lt hlo
      · have heq : (-ratio + 1 / 2) * D + D / 2 = (-ratio + 1) * D := by ring
        rw [heq] at hhi
        exact le_of_lt hhi
    exact ⟨hpath, hend⟩
  have hcomparison := iidSequenceLaw_measure_mul_le_card_mul_of_finite_block_cover
    ν (F := {()}) (prefixLength := prefixLength)
    (bridgeLength := bridgeLength) entranceSequence target
    (fun _ : Unit => entrance) (fun _ : Unit => bridge) bridgeLower
    (by intro i hi; exact hentranceMeasurable)
    (by intro i hi; exact hbridgeMeasurable)
    (by
      intro increment hincrement
      simpa [entranceSequence] using hincrement)
    (by intro i hi; simpa [bridge] using hbridge)
    (by
      intro i hi increment hevents
      apply hbridgeGeometry increment
      · simpa [entrance] using hevents.1
      · simpa [bridge] using hevents.2)
  have hcomparison' : bridgeLower * iidSequenceLaw ν entranceSequence ≤
      iidSequenceLaw ν target := by
    simpa [target] using hcomparison
  calc
    bridgeLower * entryLower = entryLower * bridgeLower := mul_comm _ _
    _ ≤ iidSequenceLaw ν entranceSequence * bridgeLower :=
      mul_le_mul_left hentrySequence _
    _ = bridgeLower * iidSequenceLaw ν entranceSequence := mul_comm _ _
    _ ≤ iidSequenceLaw ν target := hcomparison'

section StableEndpointCore

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- For a stable index-two walk, the endpoint-core estimate gives a
quantitative lower bound for the bridge from the central third of the entrance
corridor to its terminal unit-width window. For every ratio $r>1$, there are
$a>0$ and an eventual bound
\[
  \exp\!\left(\left[\frac{C}{(r/2-13/60)^2}-1\right]a^2\right)^{k_n}
  \leq \mathbb P_\nu(E_n),
\]
where $k_n=\operatorname{balancedBlockCount}(N_n-\ell_n,\ell_n)+1$ and
$\ell_n=\operatorname{stableBlockLength}(2,\nu,a^2,\mathrm{scale},n)$.
The event $E_n$ is the `InOpenPartialSumCoreReturn` block used in the
finite-variance endpoint-corridor proof.

This specialization is used in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 3, Lemma 3.5. Its stable block estimate is
Mogul'skii, Theorem 3, Section 4, p. 764, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081. -/
lemma exists_eventually_iidSequenceLaw_rightEndpointBridge_ge_stableCellLowerBound
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation 2 ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate 2 μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (ratio : ℝ) (hratio : 1 < ratio)
    (total : ℕ → ℕ) {duration : ℝ} (hduration : 0 < duration)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp
          ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
            (Combinatorics.Sequence.balancedBlockCount
              (total n - stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n)
              (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n) + 1) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              Combinatorics.Sequence.blockCoordinates 0 (total n) increment ∈
                {block |
                  RandomWalk.InOpenPartialSumCoreReturn
                    (scale n * (-ratio)) (scale n * (0 : ℝ))
                    (scale n * (-1 / 2)) (scale n * (1 / 6))
                    (scale n * (-ratio + 1 / 2)) (scale n * (1 / 2)) block}} := by
  let innerLower : ℝ := -ratio
  let innerUpper : ℝ := 0
  let startCenter : ℝ := -1 / 2
  let startRadius : ℝ := 1 / 6
  let endCenter : ℝ := -ratio + 1 / 2
  let endRadius : ℝ := 1 / 2
  let lower : ℝ := -ratio + 2 / 3 + 1 / 100
  let upper : ℝ := 1 / 3 - 1 / 100
  let epsilon : ℝ := 1 / 100
  let margin : ℝ := 1 / 100
  let delta : ℝ := 1
  have hlower : lower = innerLower + startRadius + margin - startCenter := by
    dsimp [lower, innerLower, startRadius, margin, startCenter]
    ring
  have hupper : upper = innerUpper - startRadius - margin - startCenter := by
    dsimp [upper, innerUpper, startRadius, margin, startCenter]
    ring
  have hmargin : 0 < margin := by norm_num [margin]
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hdelta : 0 < delta := by norm_num [delta]
  have hendpointBand : 3 * epsilon < (endRadius - startRadius) / 2 := by
    norm_num [epsilon, endRadius, startRadius]
  have hreturnWindows : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon := by
    intro i hi
    have hi' : (-3 : ℝ) ≤ (i : ℝ) ∧ (i : ℝ) ≤ 3 := by
      exact_mod_cast (Finset.mem_Icc.mp hi)
    constructor
    · dsimp [lower, epsilon]
      nlinarith [hratio, hi'.1]
    · dsimp [upper, epsilon]
      nlinarith [hi'.2]
  have hbridgeWindows :
      lower + 4 * epsilon < endCenter - startCenter - 4 * epsilon ∧
        endCenter - startCenter + 4 * epsilon < upper - 4 * epsilon := by
    constructor
    · dsimp [lower, epsilon, endCenter, startCenter]
      nlinarith [hratio]
    · dsimp [upper, epsilon, endCenter, startCenter]
      nlinarith [hratio]
  obtain ⟨amplitude, hamplitude, hcell⟩ :=
    exists_eventually_iidSequenceLaw_inOpenPartialSumCoreReturn_ge_exp_of_stableEscapeRate
      hscale (by norm_num) (by norm_num) hslow hEscape hX hcdf hDOA htightBase
      (innerLower := innerLower) (innerUpper := innerUpper)
      (startCenter := startCenter) (startRadius := startRadius)
      (endCenter := endCenter) (endRadius := endRadius)
      (lower := lower) (upper := upper) (epsilon := epsilon) (margin := margin)
      (delta := delta) hlower hupper hmargin hepsilon hdelta hendpointBand hreturnWindows
      hbridgeWindows total hduration htotal
  have hwidth : (upper - lower - 8 * epsilon) / 2 = ratio / 2 - 13 / 60 := by
    dsimp [upper, lower, epsilon]
    ring
  have hcoefficient :
      C / (((upper - lower - 8 * epsilon) / 2) ^ (2 : ℝ)) - delta =
        C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1 := by
    rw [hwidth]
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hcell] with n hn
  simpa only [hcoefficient, innerLower, innerUpper, startCenter, startRadius,
    endCenter, endRadius] using hn


end StableEndpointCore

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.FiniteVariance.Lemmas

end
