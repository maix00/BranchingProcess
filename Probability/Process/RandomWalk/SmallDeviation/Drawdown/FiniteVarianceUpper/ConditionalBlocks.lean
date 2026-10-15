/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
public import Probability.Process.RandomWalk.Path.Filtration
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.FiniteVarianceUpper
public import Probability.Independence.ConditionalIntegral
public import Probability.Sequence.IID.ConditionalBlocks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Conditional block bounds for bounded drawdown

The public definitions and theorems are:

- `iidSequenceLaw_condExp_prefix_nextBlock`: for an IID increment prefix
  $X$ and fresh block $Y$, $\mathbb E[f(X,Y)\mid X]=\int f(X,y)\,d\nu^{\otimes\ell}(y)$.
- `iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability`:
  a uniform section bound $p$ implies $\mathbb E[1_E\mid X]\le p$.
- `drawdownPrefixSum`, `drawdownPartialBlockSum`, and `drawdownPrefixPath`:
  finite-prefix sums and the corresponding path.
- `drawdownPastDiscretizedMaximum` and
  `measurable_drawdownPastDiscretizedMaximum`: the rounded past maximum
  $M_j$ and its measurability with respect to the prefix.
- `drawdownPastDiscretizedMaximum_eq_runningMaximum`:
  $M_j=U-w\lfloor(U-\max_{i\le j}S_i)/w\rfloor$.
- `drawdownTubePairEvent`, `drawdownTubeBlockEvent`, and
  `drawdownTubeBlockEvent_iff_path_in_interval`:
  the prefix/block tube events and their interval characterization.
- `measurableSet_drawdownTubePairEvent` and
  `measurableSet_drawdownTubeBlockEvent`: measurability of those events.
- `finiteInClosedInterval_translate_by_initial`:
  starting at $a$ translates $[l,u]$ to $[l-a,u-a]$.
- `iidSequenceLaw_map_blockCoordinates_finiteInterval_le`:
  the translated-interval probability is bounded uniformly in $a$.
- `iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_intervalBound`,
  `iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_finiteVariance`, and
  `iidSequenceLaw_condExp_drawdownTubeBlockEvent_le_of_finiteVariance`:
  the conditional block probability is at most
  $\exp(w^v-d\ell/w^2)$ for sufficiently large tube width $w$.
- `measureReal_inter_le_of_condExp_indicator_le`:
  $\mathbb E[1_E\mid\mathcal F]\le p$ implies
  $\mathbb P(A\cap E)\le p\mathbb P(A)$ for $A\in\mathcal F$.
- `drawdownConditionalBlockIntersection`,
  `measureReal_drawdownConditionalBlockIntersection_le_prod`, and
  `measureReal_drawdownConditionalBlockIntersection_le_pow`:
  the finite block intersection and its product and power bounds.

These are the conditional-expectation and Markov-property steps in Wang
Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, proof of Lemma 3.3. The one-block estimate applies
Wang Yiyang's Lemma 3.2, following Aïdékon and Hu,
*Average-weight percolation on the complete graph*, Lemma 4.1, and
Mogul'skii, *Small deviations in a space of trajectories*, Theorem 3,
Section 4, p. 764 (DOI 10.1137/1119081).
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Conditional expectation at the start of a block integrates over the
fresh block increments. This is the finite-prefix version of the Markov
property used in Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Chapter 3, proof of Lemma 3.3:
\[
  \mathbb E[f(X,Y)\mid X](\omega)
    =\int f(X(\omega),y)\,d\mathcal L(Y)(y).
\]
Here `X` is the increment prefix and `Y` is the next block of increments. -/
theorem iidSequenceLaw_condExp_prefix_nextBlock
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ)
    {f : (Fin start → ℝ) × (Fin length → ℝ) → ℝ}
    (hf : StronglyMeasurable f)
    (hfi : Integrable
      (fun increment : ℕ → ℝ =>
        f (Combinatorics.Sequence.blockCoordinates 0 start increment,
          Combinatorics.Sequence.blockCoordinates start length increment))
      (iidSequenceLaw ν)) :
    condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment : ℕ → ℝ =>
          f (Combinatorics.Sequence.blockCoordinates 0 start increment,
            Combinatorics.Sequence.blockCoordinates start length increment))
      =ᵐ[iidSequenceLaw ν]
        fun increment =>
          ∫ block, f
            (Combinatorics.Sequence.blockCoordinates 0 start increment, block)
            ∂(iidSequenceLaw ν).map
              (Combinatorics.Sequence.blockCoordinates start length) := by
  exact ProbabilityTheory.iidSequenceLaw_condExp_prefix_nextBlock
    ν start length hf hfi

/-- A uniform bound on every section of a measurable event in
`prefix × nextBlock` gives the corresponding conditional-probability bound.
The conditional expectation is evaluated by integrating the next block
against its IID law, exactly as in the Markov step of Wang Yiyang, Chapter 3,
Lemma 3.3. -/
theorem iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ)
    (E : Set ((Fin start → ℝ) × (Fin length → ℝ)))
    (hE : MeasurableSet E) {bound : ℝ}
    (hsections : ∀ past,
      ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        {block | (past, block) ∈ E} ≤ bound) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment => E.indicator (fun _ => (1 : ℝ))
          (Combinatorics.Sequence.blockCoordinates 0 start increment,
            Combinatorics.Sequence.blockCoordinates start length increment))
        increment ≤ bound := by
  let pastBlock : (ℕ → ℝ) → Fin start → ℝ :=
    Combinatorics.Sequence.blockCoordinates 0 start
  let nextBlock : (ℕ → ℝ) → Fin length → ℝ :=
    Combinatorics.Sequence.blockCoordinates start length
  let pair : (ℕ → ℝ) → (Fin start → ℝ) × (Fin length → ℝ) :=
    fun increment => (pastBlock increment, nextBlock increment)
  let f : (Fin start → ℝ) × (Fin length → ℝ) → ℝ :=
    E.indicator (fun _ => (1 : ℝ))
  have hpairMeasurable : Measurable pair := by
    exact (measurable_blockCoordinates 0 start).prodMk
      (measurable_blockCoordinates start length)
  have hpreimage : MeasurableSet (pair ⁻¹' E) := hE.preimage hpairMeasurable
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hE
  have hfi : Integrable (fun increment => f (pair increment))
      (iidSequenceLaw ν) :=
    (integrable_const (c := (1 : ℝ))).indicator hpreimage
  have hcond := iidSequenceLaw_condExp_prefix_nextBlock
    ν start length hf hfi
  have hsectionIntegral (x : Fin start → ℝ) :
      (∫ block, f (x, block) ∂
        (iidSequenceLaw ν).map nextBlock) =
        ((iidSequenceLaw ν).map nextBlock).real
          {block | (x, block) ∈ E} := by
    let sectionEvent : Set (Fin length → ℝ) := {block | (x, block) ∈ E}
    have hsectionMeasurable : MeasurableSet sectionEvent :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have hfunction : (fun block => f (x, block)) =
        sectionEvent.indicator (fun _ => (1 : ℝ)) := by
      funext block
      simp [f, sectionEvent, Set.indicator]
    rw [hfunction]
    change (∫ block, sectionEvent.indicator (fun _ => (1 : ℝ)) block
        ∂(iidSequenceLaw ν).map nextBlock) =
      ((iidSequenceLaw ν).map nextBlock).real sectionEvent
    rw [integral_indicator_const (e := (1 : ℝ)) hsectionMeasurable,
      smul_eq_mul, mul_one]
  filter_upwards [hcond] with increment hincrement
  rw [hincrement]
  have hsection := hsectionIntegral
    (Combinatorics.Sequence.blockCoordinates 0 start increment)
  rw [hsection]
  exact hsections (Combinatorics.Sequence.blockCoordinates 0 start increment)

/-- Sum of the increments in a finite prefix. -/
def drawdownPrefixSum {n : ℕ} (increments : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, increments i

/-- Sum of the increments in a finite block through the time indexed by
`k : Fin (length + 1)`. -/
def drawdownPartialBlockSum {length : ℕ} (block : Fin length → ℝ)
    (k : Fin (length + 1)) : ℝ :=
  Fin.partialSum block k

/-- The finite path generated by the increments available at a block start.
It is set to zero after that time so its running maximum depends only on the
given prefix. -/
def drawdownPrefixPath {start : ℕ} (past : Fin start → ℝ) : ℕ → ℝ :=
  fun time =>
    if htime : time ≤ start then
      drawdownPartialBlockSum past ⟨time, Nat.lt_succ_of_le htime⟩
    else 0

private theorem partialBlockSum_eq_prefixSum {length : ℕ}
    (block : Fin length → ℝ) (k : Fin (length + 1)) :
    drawdownPartialBlockSum block k =
      ∑ j : Fin k, block
        ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩ := by
  induction k using Fin.induction with
  | zero =>
      change Fin.partialSum block 0 = ∑ j : Fin 0, _
      rw [Fin.partialSum_zero, Fin.sum_univ_zero]
  | succ k ih =>
      have hrec : drawdownPartialBlockSum block k.succ =
          drawdownPartialBlockSum block k.castSucc + block k := by
        simpa only [drawdownPartialBlockSum] using Fin.partialSum_succ block k
      rw [hrec, ih]
      change (∑ j : Fin k, block ⟨j, by omega⟩) + block k =
        ∑ j : Fin ((k : ℕ) + 1), block ⟨j, by omega⟩
      rw [Fin.sum_univ_castSucc]
      congr 1

private theorem measurable_partialBlockSum {length : ℕ}
    (k : Fin (length + 1)) :
    Measurable (fun block : Fin length → ℝ =>
      drawdownPartialBlockSum block k) := by
  induction k using Fin.induction with
  | zero => exact measurable_const
  | succ k ih =>
      have hsum := ih.add (measurable_pi_apply k)
      have heq : (fun block : Fin length → ℝ =>
          drawdownPartialBlockSum block k.succ) =
        (fun block => drawdownPartialBlockSum block k.castSucc) +
          (fun block : Fin length → ℝ => block k) := by
        funext block
        simp only [drawdownPartialBlockSum, Fin.partialSum_succ, Pi.add_apply]
      exact heq ▸ hsum

private theorem measurable_prefixPath_coordinate {start : ℕ}
    (time : ℕ) :
    Measurable (fun past : Fin start → ℝ => drawdownPrefixPath past time) := by
  by_cases htime : time ≤ start
  · simpa [drawdownPrefixPath, htime] using
      measurable_partialBlockSum
        (⟨time, Nat.lt_succ_of_le htime⟩ : Fin (start + 1))
  · simp [drawdownPrefixPath, htime]

/-- The discretized maximum computed from the available finite increment
prefix. This is the `M_j` center used when conditioning at a block start. -/
noncomputable def drawdownPastDiscretizedMaximum {start : ℕ}
    (upper width : ℝ) (past : Fin start → ℝ) : ℝ :=
  spatialBinLevel upper width (drawdownPrefixPath past) start

theorem measurable_drawdownPastDiscretizedMaximum {start : ℕ}
    (upper width : ℝ) :
    Measurable (drawdownPastDiscretizedMaximum (start := start) upper width) := by
  have hmaximum : Measurable
      (fun past : Fin start → ℝ =>
        prefixMaximum (drawdownPrefixPath past) start) :=
    Finset.measurable_range_sup'' fun time htime =>
      measurable_prefixPath_coordinate time
  have hquotient : Measurable
      (fun past : Fin start → ℝ =>
        (upper - prefixMaximum (drawdownPrefixPath past) start) / width) :=
    (measurable_const.sub hmaximum).div_const width
  have hfloor : Measurable
      (fun past : Fin start → ℝ =>
        (Nat.floor ((upper - prefixMaximum (drawdownPrefixPath past) start) /
          width) : ℝ)) :=
    (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      hquotient.nat_floor
  change Measurable (fun past : Fin start → ℝ =>
    upper - width *
      (Nat.floor ((upper - prefixMaximum (drawdownPrefixPath past) start) /
        width) : ℝ))
  exact measurable_const.sub (measurable_const.mul hfloor)

private theorem prefixPath_blockCoordinates_eq
    {start : ℕ} (increment : ℕ → ℝ) {time : ℕ} (htime : time ≤ start) :
    drawdownPrefixPath
        (Combinatorics.Sequence.blockCoordinates 0 start increment) time =
      AdditivePath.displacement time increment := by
  rw [drawdownPrefixPath, dite_eq_left htime]
  change Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates 0 start increment)
        ⟨time, Nat.lt_succ_of_le htime⟩ = _
  calc
    Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates 0 start increment)
          ⟨time, Nat.lt_succ_of_le htime⟩ =
        AdditivePath.blockSum 0 time increment := by
          exact partialSum_blockCoordinates 0 increment
            ⟨time, Nat.lt_succ_of_le htime⟩
    _ = AdditivePath.displacement time increment := by
      simp [AdditivePath.blockSum_eq_displacement_natAdd]

private theorem prefixMaximum_blockCoordinates_eq
    (start : ℕ) (increment : ℕ → ℝ) :
    prefixMaximum
        (drawdownPrefixPath
          (Combinatorics.Sequence.blockCoordinates 0 start increment)) start =
      prefixMaximum (AdditivePath.displacement · increment) start := by
  unfold prefixMaximum
  exact Finset.sup'_congr
    (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ :
      (Finset.range (start + 1)).Nonempty)
    rfl
    (fun time htime => prefixPath_blockCoordinates_eq increment
      (Nat.le_of_lt_succ (Finset.mem_range.mp htime)))

theorem drawdownPastDiscretizedMaximum_eq_runningMaximum
    (start : ℕ) (upper width : ℝ) (increment : ℕ → ℝ) :
    drawdownPastDiscretizedMaximum upper width
        (Combinatorics.Sequence.blockCoordinates 0 start increment) =
      spatialBinLevel upper width (AdditivePath.displacement · increment) start := by
  simp only [drawdownPastDiscretizedMaximum, spatialBinLevel, spatialBinIndex]
  rw [prefixMaximum_blockCoordinates_eq start increment]

private theorem prefixSum_blockCoordinates_eq
    (start : ℕ) (increment : ℕ → ℝ) :
    drawdownPrefixSum
        (Combinatorics.Sequence.blockCoordinates 0 start increment) =
      AdditivePath.displacement start increment := by
  simp [drawdownPrefixSum, Combinatorics.Sequence.blockCoordinates,
    AdditivePath.displacement, Fin.sum_univ_eq_sum_range]

private theorem tubeBlockPosition_eq
    (start length : ℕ) (increment : ℕ → ℝ)
    (k : Fin (length + 1)) :
    drawdownPrefixSum
        (Combinatorics.Sequence.blockCoordinates 0 start increment) +
      drawdownPartialBlockSum
        (Combinatorics.Sequence.blockCoordinates start length increment) k =
      AdditivePath.displacement (start + (k : ℕ)) increment := by
  rw [prefixSum_blockCoordinates_eq, drawdownPartialBlockSum,
    partialSum_blockCoordinates]
  exact (AdditivePath.displacement_add_eq_add_blockSum
    start (k : ℕ) increment).symm

/-- The event for a pair consisting of a past increment prefix and the next
block: throughout the block, the walk remains in the interval
`[center(prefix) - width, center(prefix)]`. -/
def drawdownTubePairEvent {start length : ℕ}
    (center : (Fin start → ℝ) → ℝ) (width : ℝ) :
    Set ((Fin start → ℝ) × (Fin length → ℝ)) :=
  {pair | ∀ k : Fin (length + 1),
    drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k ∈
      Set.Icc (center pair.1 - width) (center pair.1)}

/-- The tube event for one increment block, with its center determined by
the increment prefix at the block's starting time. -/
def drawdownTubeBlockEvent (start length : ℕ)
    (center : (Fin start → ℝ) → ℝ) (width : ℝ) : Set (ℕ → ℝ) :=
  {increment |
    (Combinatorics.Sequence.blockCoordinates 0 start increment,
      Combinatorics.Sequence.blockCoordinates start length increment) ∈
      drawdownTubePairEvent center width}

/-- Membership in a tube block event is the requirement that the original
walk remain in the corresponding translated interval at every time from the
block start through its end. -/
theorem drawdownTubeBlockEvent_iff_path_in_interval
    (start length : ℕ) (upper binWidth tubeWidth : ℝ)
    (increment : ℕ → ℝ) :
    increment ∈ drawdownTubeBlockEvent start length
        (drawdownPastDiscretizedMaximum (start := start) upper binWidth)
        tubeWidth ↔
      ∀ k : Fin (length + 1),
        AdditivePath.displacement (start + (k : ℕ)) increment ∈
          Set.Icc
            (spatialBinLevel upper binWidth
              (AdditivePath.displacement · increment) start - tubeWidth)
            (spatialBinLevel upper binWidth
              (AdditivePath.displacement · increment) start) := by
  have hcenter :
      drawdownPastDiscretizedMaximum (start := start) upper binWidth
          (Combinatorics.Sequence.blockCoordinates 0 start increment) =
        spatialBinLevel upper binWidth
          (AdditivePath.displacement · increment) start :=
    drawdownPastDiscretizedMaximum_eq_runningMaximum
      start upper binWidth increment
  simp only [drawdownTubeBlockEvent, Set.mem_ofPred_eq,
    drawdownTubePairEvent]
  rw [hcenter]
  constructor <;> intro h k
  · simpa only [tubeBlockPosition_eq] using h k
  · simpa only [tubeBlockPosition_eq] using h k

private def blockPrefixPair (start length : ℕ) :
    (Fin (start + length) → ℝ) →
      (Fin start → ℝ) × (Fin length → ℝ) :=
  fun (whole : Fin (start + length) → ℝ) =>
    (fun i : Fin start =>
      whole (⟨(i : ℕ), by omega⟩ : Fin (start + length)),
      fun j : Fin length =>
        whole (⟨start + (j : ℕ), by omega⟩ : Fin (start + length)))

private theorem measurable_blockPrefixPair (start length : ℕ) :
    Measurable (blockPrefixPair start length) := by
  have hpast : Measurable
      (fun whole : Fin (start + length) → ℝ =>
        fun i : Fin start => whole ⟨i, by omega⟩) := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply
      (⟨(i : ℕ), by omega⟩ : Fin (start + length))
  have hblock : Measurable
      (fun whole : Fin (start + length) → ℝ =>
        fun j : Fin length => whole ⟨start + (j : ℕ), by omega⟩) := by
    rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply
      (⟨start + (j : ℕ), by omega⟩ : Fin (start + length))
  exact hpast.prodMk hblock

private theorem blockPrefixPair_blockCoordinates
    (start length : ℕ) (increment : ℕ → ℝ) :
    blockPrefixPair start length
        (Combinatorics.Sequence.blockCoordinates 0 (start + length) increment) =
      (Combinatorics.Sequence.blockCoordinates 0 start increment,
        Combinatorics.Sequence.blockCoordinates start length increment) := by
  apply Prod.ext
  · funext i
    simp [blockPrefixPair, Combinatorics.Sequence.blockCoordinates]
  · funext j
    simp [blockPrefixPair, Combinatorics.Sequence.blockCoordinates]

/-- A measurable choice of the interval center makes the next-block tube
event measurable in the past prefix and block increments. -/
theorem measurableSet_drawdownTubePairEvent {start length : ℕ}
    (center : (Fin start → ℝ) → ℝ) (hcenter : Measurable center)
    (width : ℝ) : MeasurableSet
      (drawdownTubePairEvent (start := start) (length := length) center width) := by
  rw [show drawdownTubePairEvent (start := start) (length := length)
        center width =
      ⋂ k : Fin (length + 1),
        {pair : (Fin start → ℝ) × (Fin length → ℝ) |
          drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k ∈
            Set.Icc (center pair.1 - width) (center pair.1)} by
    ext pair
    simp [drawdownTubePairEvent]]
  apply MeasurableSet.iInter
  intro k
  have hpast : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) => drawdownPrefixSum pair.1) := by
    exact ((Finset.measurable_sum Finset.univ fun i _ =>
      measurable_pi_apply i).comp measurable_fst)
  have hblock : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) => drawdownPartialBlockSum pair.2 k) := by
    exact (measurable_partialBlockSum k).comp measurable_snd
  have hcenterValue : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) => center pair.1) :=
    hcenter.comp measurable_fst
  have hvalue : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k) :=
    hpast.add hblock
  have hlower : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k -
          (center pair.1 - width)) :=
    hvalue.sub (hcenterValue.sub measurable_const)
  have hupper : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k -
          center pair.1) := hvalue.sub hcenterValue
  have heq :
      {pair : (Fin start → ℝ) × (Fin length → ℝ) |
        drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k ∈
          Set.Icc (center pair.1 - width) (center pair.1)} =
      {pair | 0 ≤ drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k -
          (center pair.1 - width) ∧
        drawdownPrefixSum pair.1 + drawdownPartialBlockSum pair.2 k -
          center pair.1 ≤ 0} := by
    ext pair
    simp only [Set.mem_Icc, Set.mem_ofPred_eq]
    constructor <;> intro h <;> constructor <;> linarith
  rw [heq]
  exact (measurableSet_Ici.preimage hlower).inter
    (measurableSet_Iic.preimage hupper)

/-- A tube block event is measurable at the end of its increment block, so
it can serve as the next event in the conditional-expectation recursion over
the natural domain filtration. -/
theorem measurableSet_drawdownTubeBlockEvent
    (start length : ℕ) (center : (Fin start → ℝ) → ℝ)
    (hcenter : Measurable center) (width : ℝ) :
    MeasurableSet[ProbabilityTheory.sequencePrefixFiltration
      (E := ℝ) (start + length)]
      (drawdownTubeBlockEvent start length center width) := by
  have hpairEvent : MeasurableSet
      (drawdownTubePairEvent (start := start) (length := length)
        center width) :=
    measurableSet_drawdownTubePairEvent
      (start := start) (length := length) center hcenter width
  have hpreimage : MeasurableSet
      ((blockPrefixPair start length) ⁻¹'
        drawdownTubePairEvent center width) :=
    hpairEvent.preimage (measurable_blockPrefixPair start length)
  have hevent : drawdownTubeBlockEvent start length center width =
      (Combinatorics.Sequence.blockCoordinates 0 (start + length)) ⁻¹'
        ((blockPrefixPair start length) ⁻¹'
          drawdownTubePairEvent center width) := by
    ext increment
    simp only [drawdownTubeBlockEvent, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← blockPrefixPair_blockCoordinates start length increment]
  rw [ProbabilityTheory.sequencePrefixFiltration_eq_comap_blockCoordinates]
  exact (MeasurableSpace.measurableSet_comap).2
    ⟨_, hpreimage, hevent.symm⟩

/-- A translated finite interval event has the same membership condition
after subtracting its initial position from both interval endpoints. -/
theorem finiteInClosedInterval_translate_by_initial
    {length : ℕ} (lower upper initial : ℝ)
    (block : Fin length → ℝ) :
    FiniteInClosedInterval lower upper initial block ↔
      FiniteInClosedInterval (lower - initial) (upper - initial) 0 block := by
  simp only [FiniteInClosedInterval, Set.mem_Icc]
  constructor <;> intro h k
  · have hk := h k
    constructor <;> linarith
  · have hk := h k
    constructor <;> linarith

/-- The law of a finite coordinate block assigns the same mass to the
finite-path interval event as the infinite IID law assigns to the associated
partial-sum interval event. -/
theorem iidSequenceLaw_map_blockCoordinates_finiteInterval_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {length : ℕ} {lower upper : ℝ}
    (hzero : (0 : ℝ) ∈ Set.Icc lower upper)
    {bound : ℝ≥0∞}
    (hbound : iidSequenceLaw ν
      {increment : ℕ → ℝ | ∀ j : Fin length,
        AdditivePath.displacement (j + 1) increment ∈ Set.Icc lower upper} ≤
      bound) :
    ((iidSequenceLaw ν).map
      (Combinatorics.Sequence.blockCoordinates 0 length))
      {block | FiniteInClosedInterval lower upper 0 block} ≤ bound := by
  have hfinite : MeasurableSet
      {block : Fin length → ℝ | FiniteInClosedInterval lower upper 0 block} :=
    measurableSet_finiteInClosedInterval lower upper 0 length
  have hevent :
      {increment : ℕ → ℝ |
        FiniteInClosedInterval lower upper 0
          (Combinatorics.Sequence.blockCoordinates 0 length increment)} =
      {increment | ∀ j : Fin length,
        AdditivePath.displacement (j + 1) increment ∈ Set.Icc lower upper} := by
    ext increment
    have hbridge := finiteInClosedInterval_blockCoordinates_iff
      lower upper 0 0 length increment
    have hstays := staysIn_Icc_iff_inClosedInterval
      lower upper length 0 hzero (fun k => increment (0 + k))
    constructor
    · intro h
      have hpath := hbridge.mp h
      have hstay := hstays.mpr hpath
      simpa [StaysIn, Nat.zero_add] using hstay
    · intro h
      have hstay : StaysIn (Set.Icc lower upper) length 0
          (fun k => increment (0 + k)) := by
        simpa [StaysIn, Nat.zero_add] using h
      exact hbridge.mpr (hstays.mp hstay)
  calc
    _ = iidSequenceLaw ν
        {increment | FiniteInClosedInterval lower upper 0
          (Combinatorics.Sequence.blockCoordinates 0 length increment)} := by
      rw [Measure.map_apply (measurable_blockCoordinates 0 length) hfinite]
      rfl
    _ = iidSequenceLaw ν
        {increment | ∀ j : Fin length,
          AdditivePath.displacement (j + 1) increment ∈ Set.Icc lower upper} := by
      rw [hevent]
    _ ≤ bound := hbound

/-- Lemma 3.2's uniform translated-interval estimate bounds the
conditional probability of the next tube block, even when its upper endpoint
is selected measurably from the past. The time-zero constraint contributes
conditional probability zero whenever the current position is outside the
chosen interval. -/
theorem iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_intervalBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ)
    (center : (Fin start → ℝ) → ℝ) (hcenter : Measurable center)
    (width bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hinterval : ∀ lower : ℝ, lower ≤ 0 → 0 ≤ lower + width →
      ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates 0 length))
        {block | FiniteInClosedInterval lower (lower + width) 0 block} ≤
          ENNReal.ofReal bound) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment =>
          (drawdownTubePairEvent center width).indicator (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment))
        increment ≤ bound := by
  have hE : MeasurableSet
      (drawdownTubePairEvent (start := start) (length := length)
        center width) :=
    measurableSet_drawdownTubePairEvent center hcenter width
  have hsections : ∀ past,
      ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        {block | (past, block) ∈ drawdownTubePairEvent center width} ≤ bound := by
    intro past
    let initial := drawdownPrefixSum past
    let top := center past
    let sectionEvent : Set (Fin length → ℝ) :=
      {block | (past, block) ∈ drawdownTubePairEvent center width}
    have hsectionEq : sectionEvent =
        {block | FiniteInClosedInterval (top - width) top initial block} := by
      ext block
      simp only [sectionEvent, drawdownTubePairEvent, FiniteInClosedInterval,
        Set.mem_ofPred_eq, Set.mem_Icc]
      constructor <;> intro h k
      · have hk := h k
        simpa only [initial, top, drawdownPrefixSum,
          partialBlockSum_eq_prefixSum] using hk
      · have hk := h k
        simpa only [initial, top, drawdownPrefixSum,
          partialBlockSum_eq_prefixSum] using hk
    by_cases hstart : initial ∈ Set.Icc (top - width) top
    · let lower := top - width - initial
      have hlower : lower ≤ 0 := by
        dsimp [lower]
        exact sub_nonpos.mpr hstart.1
      have hupper : 0 ≤ lower + width := by
        dsimp [lower]
        linarith [hstart.2]
      have hendpoint : lower + width = top - initial := by
        dsimp [lower]
        ring
      have htranslate : sectionEvent =
          {block | FiniteInClosedInterval lower (lower + width) 0 block} := by
        rw [hsectionEq]
        ext block
        have htrans := finiteInClosedInterval_translate_by_initial
          (top - width) top initial block
        simpa [lower, hendpoint] using htrans
      have hprobability :
          ((iidSequenceLaw ν).map
            (Combinatorics.Sequence.blockCoordinates start length))
            sectionEvent ≤ ENNReal.ofReal bound := by
        rw [iidSequenceLaw_map_blockCoordinates ν start length]
        simpa [htranslate] using hinterval lower hlower hupper
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprobability
      simpa [Measure.real, ENNReal.toReal_ofReal hboundNonneg] using hreal
    · have hempty : sectionEvent = ∅ := by
        ext block
        constructor
        · intro hmem
          have hinitial := hmem ⟨0, Nat.zero_lt_succ _⟩
          have hinitialMem : initial ∈ Set.Icc (top - width) top := by
            simpa [initial, top, drawdownPrefixSum,
              drawdownPartialBlockSum] using hinitial
          exact (hstart hinitialMem).elim
        · simp
      change ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real sectionEvent ≤ bound
      rw [hempty]
      simpa [Measure.real] using hboundNonneg
  exact iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability
    ν start length (drawdownTubePairEvent center width) hE hsections

/-- Applying the translated-interval estimate of Wang Yiyang, *Asymptotic
speed of the $N$-branching random walk with infinite offspring*, Chapter 3,
Lemma 3.2, bounds the conditional probability of each tube block in the
Lemma 3.3 decomposition. -/
theorem iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ width₀ : ℝ, 0 < width₀ ∧
      ∀ width : ℝ, width₀ ≤ width → ∀ length : ℕ, 1 ≤ length →
      ∀ start : ℕ, ∀ center : (Fin start → ℝ) → ℝ,
        Measurable center →
        ∀ᵐ increment ∂iidSequenceLaw ν,
          condExp
            (MeasurableSpace.comap
              (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
            (iidSequenceLaw ν)
            (fun increment =>
              (drawdownTubePairEvent center width).indicator
                (fun _ => (1 : ℝ))
                (Combinatorics.Sequence.blockCoordinates 0 start increment,
                  Combinatorics.Sequence.blockCoordinates start length increment))
            increment ≤ Real.exp (width ^ v - d * ((length : ℝ) / width ^ 2)) := by
  have hvariance' : 0 < ∫ x : ℝ, x ^ 2 ∂ν := by
    rw [hν.2]
    exact hvariance
  obtain ⟨width₀, hwidth₀, hintervalBound⟩ :=
    iidSequenceLaw_intervalProbability_le_exp_of_finiteVariance
      ν hν.1 hsquare hvariance' hv hd (by simpa [hν.2] using hcritical)
  refine ⟨width₀, hwidth₀, ?_⟩
  intro width hwidth length hlength start center hcenter
  apply iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_intervalBound
    ν start length center hcenter width
    (Real.exp (width ^ v - d * ((length : ℝ) / width ^ 2))) (by positivity)
  intro lower hlower hupper
  exact iidSequenceLaw_map_blockCoordinates_finiteInterval_le ν
    ⟨hlower, hupper⟩
    (hintervalBound width hwidth lower hlower hupper length hlength)

/-- The block-event form of the Lemma 3.2 estimate, conditioned on the
natural domain filtration at the block's starting time. -/
theorem iidSequenceLaw_condExp_drawdownTubeBlockEvent_le_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ width₀ : ℝ, 0 < width₀ ∧
      ∀ width : ℝ, width₀ ≤ width → ∀ length : ℕ, 1 ≤ length →
      ∀ start : ℕ, ∀ center : (Fin start → ℝ) → ℝ,
        Measurable center →
        ∀ᵐ increment ∂iidSequenceLaw ν,
          condExp
            (ProbabilityTheory.sequencePrefixFiltration (E := ℝ) start)
            (iidSequenceLaw ν)
            ((drawdownTubeBlockEvent start length center width).indicator
              (fun _ => (1 : ℝ))) increment ≤
            Real.exp (width ^ v - d * ((length : ℝ) / width ^ 2)) := by
  obtain ⟨width₀, hwidth₀, hbound⟩ :=
    iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_finiteVariance
      ν hν hsquare hvariance hv hd hcritical
  refine ⟨width₀, hwidth₀, ?_⟩
  intro width hwidth length hlength start center hcenter
  rw [ProbabilityTheory.sequencePrefixFiltration_eq_comap_blockCoordinates]
  have hindicator :
      (drawdownTubeBlockEvent start length center width).indicator
          (fun _ => (1 : ℝ)) =
        fun increment =>
          (drawdownTubePairEvent center width).indicator (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment) := by
    funext increment
    rfl
  filter_upwards [hbound width hwidth length hlength start center hcenter]
    with increment hincrement
  rw [hindicator]
  exact hincrement

/-- If the conditional probability of the next event is at most `p` on a
measurable past event `A`, integration over `A` gives
`P (A ∩ E) ≤ p * P A`. This is the tower-property step iterated over the
good blocks in Wang Yiyang, Chapter 3, proof of Lemma 3.3. -/
theorem measureReal_inter_le_of_condExp_indicator_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {A E : Set Ω} (hA : MeasurableSet[m] A)
    (hE : MeasurableSet[mΩ] E)
    {p : ℝ}
    (hcond : ∀ᵐ ω ∂P, ω ∈ A →
      condExp m P (E.indicator fun _ => (1 : ℝ)) ω ≤ p) :
    P.real (A ∩ E) ≤ p * P.real A := by
  let f : Ω → ℝ := E.indicator fun _ => (1 : ℝ)
  have hf : Integrable f P :=
    (integrable_const (c := (1 : ℝ))).indicator hE
  have hAE : MeasurableSet[mΩ] (A ∩ E) := (hm A hA).inter hE
  have hindicator : (A ∩ E).indicator (fun _ => (1 : ℝ)) = A.indicator f := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωE : ω ∈ E <;>
      simp [f, hωA, hωE]
  calc
    P.real (A ∩ E) = ∫ ω, (A ∩ E).indicator (fun _ => (1 : ℝ)) ω ∂P :=
      (integral_indicator_one hAE).symm
    _ = ∫ ω in A, f ω ∂P := by
      rw [hindicator, integral_indicator (hm A hA)]
    _ = ∫ ω in A, condExp m P f ω ∂P :=
      (setIntegral_condExp hm hf hA).symm
    _ ≤ ∫ ω in A, p ∂P := by
      apply setIntegral_mono_on_ae
      · exact integrable_condExp.integrableOn
      · exact (integrable_const p).integrableOn
      · exact hm A hA
      · exact hcond
    _ = p * P.real A := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- The intersection of the first `n` block events in a conditional
expectation iteration. -/
def drawdownConditionalBlockIntersection
    {Ω : Type*} [MeasurableSpace Ω]
    (events : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => Set.univ
  | n + 1 => drawdownConditionalBlockIntersection events n ∩ events n

/-- Conditional integration over the first `n` blocks bounds the
intersection by the product of the individual conditional bounds. -/
theorem measureReal_drawdownConditionalBlockIntersection_le_prod
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    (bounds : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bounds n)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      condExp (filtration n) P
        ((events n).indicator fun _ => (1 : ℝ)) ω ≤ bounds n)
    (n : ℕ) :
    P.real (drawdownConditionalBlockIntersection events n) ≤
      ∏ j ∈ Finset.range n, bounds j := by
  have hmeas : ∀ n,
      MeasurableSet[filtration n]
        (drawdownConditionalBlockIntersection events n) := by
    intro n
    induction n with
    | zero => simp [drawdownConditionalBlockIntersection]
    | succ n ih =>
        rw [drawdownConditionalBlockIntersection]
        exact (hfiltrationMono n _ ih).inter (heventMeasurable n)
  induction n with
  | zero => simp [drawdownConditionalBlockIntersection]
  | succ n ih =>
      rw [drawdownConditionalBlockIntersection]
      have hconditionalOnPrefix : ∀ᵐ ω ∂P,
          ω ∈ drawdownConditionalBlockIntersection events n →
            condExp (filtration n) P
              ((events n).indicator fun _ => (1 : ℝ)) ω ≤ bounds n := by
        filter_upwards [hconditional n] with ω hω
        intro _
        exact hω
      calc
        P.real
            (drawdownConditionalBlockIntersection events n ∩ events n) ≤
            bounds n * P.real (drawdownConditionalBlockIntersection events n) :=
          measureReal_inter_le_of_condExp_indicator_le
            (filtration n) (hfiltrationAmbient n) (hmeas n)
            (hfiltrationAmbient (n + 1) (events n)
              (heventMeasurable n)) hconditionalOnPrefix
        _ ≤ bounds n * (∏ j ∈ Finset.range n, bounds j) :=
          mul_le_mul_of_nonneg_left ih (hboundNonneg n)
        _ = ∏ j ∈ Finset.range (n + 1), bounds j := by
          rw [Finset.prod_range_succ]
          ring

/-- If each next-block event is measurable at its block end and has
conditional probability at most `p` given the preceding domain, the
conditional-expectation recursion yields
\[
  \mathbb P\!\left(\bigcap_{j=0}^{n-1}E_j\right)\leq p^n.
\]
This is the iteration used for the complement of the jump set in the proof
of Wang Yiyang, Chapter 3, Lemma 3.3. The conditional bounds are imposed on
the whole sample space; for a tube event, its time-zero constraint makes the
conditional probability zero whenever the starting point lies outside the
interval. -/
theorem measureReal_drawdownConditionalBlockIntersection_le_pow
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    {p : ℝ} (hp : 0 ≤ p)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      condExp (filtration n) P (events n |>.indicator fun _ => (1 : ℝ)) ω ≤ p)
    (n : ℕ) :
    P.real (drawdownConditionalBlockIntersection events n) ≤ p ^ n := by
  have hprod := measureReal_drawdownConditionalBlockIntersection_le_prod
    filtration hfiltrationMono hfiltrationAmbient events heventMeasurable
    (fun _ => p) (fun _ => hp) hconditional n
  simpa [Finset.prod_const, Finset.card_range] using hprod

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
