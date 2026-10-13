/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Drawdown
public import Probability.Process.RandomWalk.Path.Filtration
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.FiniteVarianceUpper
public import Probability.Independence.ConditionalIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Bounded-drawdown walk events

Public theorem declarations (write `S_i` for the additive path and `P` for its IID law):

- `iidSequenceLaw_condExp_prefix_nextBlock`: `E[f(X,Y) | X] = ∫ f(X,y) dν^ℓ(y)`.
- `iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability`: section bounds `≤ p`
  give `E[1_E | X] ≤ p`.
- `measurable_drawdownPastDiscretizedMaximum`: the rounded past maximum `M_j` is measurable.
- `drawdownPastDiscretizedMaximum_eq_runningMaximum`:
  `M_j = U - w ⌊(U - max_{i≤j} S_i)/w⌋`.
- `drawdownTubeBlockEvent_iff_path_in_interval`: a tube event is the interval
  condition `M_j-w-Δ ≤ S_i ≤ M_j` throughout its block.
- `measurableSet_drawdownTubePairEvent`: the prefix/block tube event is measurable.
- `measurableSet_drawdownTubeBlockEvent`: the full-path tube event is measurable.
- `finiteInClosedInterval_translate_by_initial`: `S_i ∈ [l,u]` from `a` is
  equivalent to `S_i-a ∈ [l-a,u-a]` from zero.
- `iidSequenceLaw_map_blockCoordinates_finiteInterval_le`: interval-block
  probability is at most its uniform translated-interval bound.
- `iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_intervalBound`:
  a uniform interval bound `p` gives `E[1_E | X] ≤ p`.
- `iidSequenceLaw_condExp_drawdownTubePairEvent_le_of_finiteVariance`:
  `E[1_E | X] ≤ exp(w^v-dℓ/w²)` for sufficiently large `w`.
- `iidSequenceLaw_condExp_drawdownTubeBlockEvent_le_of_finiteVariance`:
  `E[1_{E_j} | F_j] ≤ exp(w^v-dℓ/w²)`.
- `measureReal_inter_le_of_condExp_indicator_le`:
  `E[1_E | F] ≤ p` gives `P(A ∩ E) ≤ p P(A)` for `A ∈ F`.
- `measureReal_drawdownConditionalBlockIntersection_le_prod`:
  `P(⋂_j E_j) ≤ ∏_j p_j`.
- `measureReal_drawdownConditionalBlockIntersection_le_pow`:
  with a common factor, `P(⋂_j E_j) ≤ p^q`.
- `drawdownBlockStart_last_eq_horizon`: the remainder plus `qℓ` equals `L`.
- `eventually_drawdownFloorBlockLength_bounds`: for `η>0`,
  `Δ^(2+η/2) ≤ ⌊Δ^(2+η)⌋ ≤ Δ^(2+η)` for large `Δ`.
- `drawdown_prod_jumpPatternBound_eq_pow`: the block product is `p^(q-|J|)`.
- `drawdown_prod_jumpPatternBound_le_pow`: `|J| ≤ K`, `p ≤ 1` give
  `p^(q-|J|) ≤ p^(q-K)`.
- `measureReal_drawdownJumpPatternTubeIntersection_le_prod`:
  `P(E_J) ≤ ∏_j p_j` for a fixed jump pattern.
- `drawdownBlockTubeCondition_implies_tubeBlockEvent`: constant `M_j`
  imposes the tube condition on the next block.
- `drawdown_card_maximumJumpSet_le`: the number of maximum jumps is `≤ K`.
- `drawdown_discretizedMaximumBlockDecomposition`: a bounded-drawdown
  path admits rounded maxima with at most `K` jumps.
- `additivePath_le_threshold_add_delta_of_noLargeDrop`:
  `S_L ≤ r` and drawdown `≤ Δ` imply `S_i ≤ r+Δ`.
- `neg_delta_le_additivePath_of_noLargeDrop`: drawdown `≤ Δ` gives `S_i ≥ -Δ`.
- `blockOscillationEvent_of_additiveSegment`: bounded segment oscillation
  gives the corresponding increment-block oscillation event.
- `drawdown_event_discretizedMaximumBlockDecomposition`:
  `B_{L,Δ,r}` has the rounded-maximum decomposition.
- `drawdown_event_goodBlocks_satisfy_tubeCondition`:
  on `B_{L,Δ,r}`, a nonjump block lies in its width `w+Δ` tube.
- `drawdown_mem_jumpPatternTubeIntersection_of_goodBlocks`:
  `B_{L,Δ,r} ∩ {J=J₀} ⊆ E_{J₀}`.
- `drawdown_noLargeDropEvent_subset_jumpPatternUnion`:
  `B_{L,Δ,r} ⊆ ⋃_{|J₀|≤K} E_{J₀}`.
- `measureReal_noLargeDropEvent_le_sum_jumpPatternProducts`:
  `P(B_{L,Δ,r}) ≤ ∑_{|J₀|≤K} ∏_j p_j`.
- `measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow`:
  `P(B_{L,Δ,r}) ≤ 2^q p^(q-K)` when `p ≤ 1`.
- `measureReal_noLargeDropEvent_le_exp_of_blockParameters`:
  explicit entropy and jump-count bounds give `P(B_{L,Δ,r}) ≤ exp(-d z)`.
- `measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance`:
  for large `Δ` and `L ≥ Δ^(2+c)`, `P(B_{L,Δ,Δ/c}) ≤ exp(-d L/Δ²)`.
- `exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment`:
  for `ρ,p>0`, a centered law with variance `σ²`, and `target<π²/2`, uniformly
  for large `Δ` and `L ≥ Δ^(2+p)`,
  `P(B_{L,Δ,Δ/ρ}) ≤ exp(-target·σ²L/Δ²)`.
- `tendsto_diffusiveBlockCount_atTop_of_horizonRatio`:
  `L_n/Δ_n² → ∞` gives `L_n/⌊AΔ_n²⌋ → ∞` when `Δ_n → ∞`, `A > 0`.

For the additive path \(S_j=\sum_{i<j}\xi_i\),
`noLargeDropEndpointBelowEvent L Δ r` is
\[
  B_{L,\Delta,r}:=\{\xi:\ S_i-S_j\leq\Delta\ (0\leq i\leq j\leq L),\ S_L\leq r\}.
\]
The public estimates formalize the deterministic bounds on \(B_{L,\Delta,r}\),
the block decomposition in the proof of Wang Yiyang, *Asymptotic speed of the
\(N\)-branching random walk with infinite offspring*, Chapter 3, Lemma 3.3,
and the finite jump-pattern estimate for the drawdown endpoint event: with
\(q=\lfloor L/\ell\rfloor\),
\(K=\lfloor(r+\Delta)/w\rfloor+1\), and
\(p=\exp((w+\Delta)^v-d\ell/(w+\Delta)^2)\),
\[
  \mathbb P(B_{L,\Delta,r})\leq 2^q p^{q-K}\qquad (p\leq1).
\]
Here \(w\) is the spatial bin width, \(\ell\) is the block length, and the
rounded maximum at block \(j\) is
\(M_j=U-w\lfloor(U-\max_{i\leq r_0+j\ell}S_i)/w\rfloor\), where \(r_0\) is
the initial remainder. The unchanged-maximum blocks satisfy
\(M_j-w-\Delta<S_i\leq M_j\). The final lemma gives
\[
  \frac{L_n}{\lfloor A\Delta_n^2\rfloor}\longrightarrow\infty
  \quad\text{when}\quad
  \Delta_n\longrightarrow\infty,\qquad
  \frac{L_n}{\Delta_n^2}\longrightarrow\infty,
\]
which supplies the block-count limit used by the proof layer for Lemma 3.3.
The finite-variance theorem formalizes Lemma 3.3 of Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, extending Lemma 2.3 of Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, Lemma 2.3
(2025, arXiv:2512.23266): for a centered increment law of variance `σ² > 0`,
`c > 0`, and `0 < d < π²σ²/2`,
\[
  \mathbb P\!\left(Y_L\leq\frac{\Delta}{c},\quad
    \min_{0\leq i\leq j\leq L}(Y_j-Y_i)\geq-\Delta\right)
  \leq \exp\!\left(-d\frac{L}{\Delta^2}\right)
\]
for all sufficiently large `Δ` and `L ≥ Δ^(2+c)`. Its discretized-maximum
block decomposition follows Wang Yiyang, *Asymptotic speed of the
N-branching random walk with infinite offspring*, Chapter 3, Lemma 3.3; its
one-block estimate combines Wang Yiyang, Chapter 3, Lemma 3.2, Aïdékon and
Hu, *Average-weight percolation on the complete graph*, Lemma 4.1, and
Mogul'skii, *Small deviations in a space of trajectories*, Theorem 3,
Section 4, p. 764 (English translation, *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081).
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
  have hblock : Measurable
      (Combinatorics.Sequence.blockCoordinates (E := ℝ) (0 + start) length) := by
    simpa only [Nat.zero_add] using
      (measurable_blockCoordinates (E := ℝ) start length)
  have hfi' : Integrable
      (fun sample : ℕ → ℝ =>
        f (Combinatorics.Sequence.blockCoordinates 0 start sample,
          Combinatorics.Sequence.blockCoordinates (0 + start) length sample))
      (iidSequenceLaw ν) := by
    simpa only [Nat.zero_add] using hfi
  have hcond := (indepFun_blockCoordinates_blockCoordinates ν 0 start length)
    |>.condExp_prod_ae_eq_integral_map
      (measurable_blockCoordinates (E := ℝ) 0 start)
      hblock hf hfi'
  simpa only [Nat.zero_add] using hcond

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

/-- The start time of block `j` in the decomposition used in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, Lemma 3.3. The initial remainder is followed by equal blocks. -/
def drawdownBlockStart (remainder blockLength j : ℕ) : ℕ :=
  remainder + j * blockLength

/-- The number of complete blocks of length `blockLength` in a horizon. -/
def drawdownBlockCount (horizon blockLength : ℕ) : ℕ :=
  horizon / blockLength

/-- The initial remainder in the Lemma 3.3 block decomposition. -/
def drawdownBlockRemainder (horizon blockLength : ℕ) : ℕ :=
  horizon % blockLength

/-- The remainder and complete blocks end exactly at the horizon. -/
theorem drawdownBlockStart_last_eq_horizon {horizon blockLength : ℕ} :
    drawdownBlockStart (drawdownBlockRemainder horizon blockLength)
      blockLength (drawdownBlockCount horizon blockLength) = horizon := by
  simp [drawdownBlockStart, drawdownBlockRemainder, drawdownBlockCount,
    Nat.mod_add_div, Nat.mul_comm]

/-- The rounded running maximum `M_j` from the proof of Wang Yiyang,
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
theorem drawdown_prod_jumpPatternBound_eq_pow {q : ℕ}
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
theorem drawdown_prod_jumpPatternBound_le_pow {q K : ℕ}
    (pattern : Finset (Fin q)) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcard : pattern.card ≤ K) :
    (∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
      p ^ (q - K) := by
  rw [drawdown_prod_jumpPatternBound_eq_pow]
  exact pow_le_pow_of_le_one hp0 hp1 (by omega)

/-- For a fixed jump pattern, conditional integration contributes the
Lemma 3.2 tube bound on each nonjump block and the factor one on jump
blocks. This is the block-by-block estimate in Wang Yiyang, *Asymptotic
speed of the $N$-branching random walk with infinite offspring*, Chapter 3,
proof of Lemma 3.3. -/
private theorem measureReal_drawdownJumpPatternTubeIntersection_le_prod_of_uniformBlockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {v d tubeWidth₀ : ℝ}
    (hblockBound : ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ length : ℕ, 1 ≤ length → ∀ start : ℕ,
      ∀ center : (Fin start → ℝ) → ℝ, Measurable center →
      ∀ᵐ increment ∂iidSequenceLaw ν,
        condExp
          (ProbabilityTheory.sequencePrefixFiltration (E := ℝ) start)
          (iidSequenceLaw ν)
          ((drawdownTubeBlockEvent start length center tubeWidth).indicator
            (fun _ => (1 : ℝ))) increment ≤
          Real.exp (tubeWidth ^ v - d * ((length : ℝ) / tubeWidth ^ 2)))
    (remainder q blockLength : ℕ) (hblockLength : 1 ≤ blockLength) :
    ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ upper binWidth : ℝ, ∀ pattern : Finset (Fin q),
        (iidSequenceLaw ν).real
          (drawdownConditionalBlockIntersection
            (drawdownJumpPatternTubeEvent remainder blockLength pattern
              upper binWidth tubeWidth) q) ≤
          ∏ j ∈ Finset.range q,
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ v -
                d * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
  intro tubeWidth htubeWidth upper binWidth pattern
  let filtration : ℕ → MeasurableSpace (ℕ → ℝ) :=
    fun n => ProbabilityTheory.sequencePrefixFiltration (E := ℝ)
      (remainder + n * blockLength)
  let events : ℕ → Set (ℕ → ℝ) :=
    drawdownJumpPatternTubeEvent remainder blockLength pattern
      upper binWidth tubeWidth
  let p := Real.exp (tubeWidth ^ v -
    d * ((blockLength : ℝ) / tubeWidth ^ 2))
  let bounds : ℕ → ℝ := fun n => drawdownJumpPatternBound pattern p n
  have hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1) := by
    intro n
    dsimp [filtration]
    apply (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).mono'
    have htime : remainder + n * blockLength + blockLength =
        remainder + (n + 1) * blockLength := by
      simp [Nat.add_mul, Nat.add_assoc]
    rw [← htime]
    exact Nat.le_add_right _ _
  have hfiltrationAmbient : ∀ n,
      filtration n ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
    intro n
    exact (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).le'
      (remainder + n * blockLength)
  have heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n) := by
    intro n
    have htime : remainder + (n + 1) * blockLength =
        remainder + n * blockLength + blockLength := by
      simp [Nat.add_mul, Nat.add_assoc]
    change MeasurableSet[ProbabilityTheory.sequencePrefixFiltration
      (E := ℝ) (remainder + (n + 1) * blockLength)]
      (drawdownJumpPatternTubeEvent remainder blockLength pattern
        upper binWidth tubeWidth n)
    by_cases hn : n < q
    · by_cases hjump : (⟨n, hn⟩ : Fin q) ∈ pattern
      · simp [drawdownJumpPatternTubeEvent, hn, hjump]
      · rw [htime]
        simpa [drawdownJumpPatternTubeEvent, hn, hjump] using
          measurableSet_drawdownTubeBlockEvent
          (remainder + n * blockLength) blockLength
          (drawdownPastDiscretizedMaximum
            (start := remainder + n * blockLength) upper binWidth)
          (measurable_drawdownPastDiscretizedMaximum upper binWidth) tubeWidth
    · simp [drawdownJumpPatternTubeEvent, hn]
  have hboundNonneg : ∀ n, 0 ≤ bounds n := by
    intro n
    by_cases hn : n < q
    · by_cases hjump : (⟨n, hn⟩ : Fin q) ∈ pattern
      · simp [bounds, drawdownJumpPatternBound, hn, hjump]
      · simp [bounds, drawdownJumpPatternBound, hn, hjump, p]
        positivity
    · simp [bounds, drawdownJumpPatternBound, hn]
  have hconditional : ∀ n, ∀ᵐ increment ∂iidSequenceLaw ν,
      condExp (filtration n) (iidSequenceLaw ν)
        ((events n).indicator (fun _ => (1 : ℝ))) increment ≤ bounds n := by
    intro n
    by_cases hn : n < q
    · by_cases hjump : (⟨n, hn⟩ : Fin q) ∈ pattern
      · have hconst := condExp_const (μ := iidSequenceLaw ν)
          (hfiltrationAmbient n) (1 : ℝ)
        have hconstAE : ∀ᵐ increment ∂iidSequenceLaw ν,
            condExp (filtration n) (iidSequenceLaw ν)
              (fun _ => (1 : ℝ)) increment = 1 := by
          rw [hconst]
          exact Filter.Eventually.of_forall (fun _ => rfl)
        have hevent : events n = Set.univ := by
          simp [events, drawdownJumpPatternTubeEvent, hn, hjump]
        rw [hevent]
        filter_upwards [hconstAE] with increment hvalue
        simpa [bounds, drawdownJumpPatternBound, hn, hjump] using hvalue.le
      · filter_upwards
          [hblockBound tubeWidth htubeWidth blockLength hblockLength
            (remainder + n * blockLength)
            (drawdownPastDiscretizedMaximum
              (start := remainder + n * blockLength) upper binWidth)
            (measurable_drawdownPastDiscretizedMaximum upper binWidth)]
          with increment hbound
        simpa [events, bounds, p, drawdownJumpPatternTubeEvent,
          drawdownJumpPatternBound, hn, hjump, filtration] using hbound
    · have hconst := condExp_const (μ := iidSequenceLaw ν)
        (hfiltrationAmbient n) (1 : ℝ)
      have hconstAE : ∀ᵐ increment ∂iidSequenceLaw ν,
          condExp (filtration n) (iidSequenceLaw ν)
            (fun _ => (1 : ℝ)) increment = 1 := by
        rw [hconst]
        exact Filter.Eventually.of_forall (fun _ => rfl)
      have hevent : events n = Set.univ := by
        simp [events, drawdownJumpPatternTubeEvent, hn]
      rw [hevent]
      filter_upwards [hconstAE] with increment hvalue
      simpa [bounds, drawdownJumpPatternBound, hn] using hvalue.le
  exact measureReal_drawdownConditionalBlockIntersection_le_prod
    filtration hfiltrationMono hfiltrationAmbient events heventMeasurable
    bounds hboundNonneg hconditional q

/-- Conditional block estimates from Wang Yiyang, *Asymptotic speed of the
$N$-branching random walk with infinite offspring*, Chapter 3, Lemma 3.3,
give a uniform tube-width threshold for each fixed finite block decomposition. -/
theorem measureReal_drawdownJumpPatternTubeIntersection_le_prod
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance)
    (remainder q blockLength : ℕ) (hblockLength : 1 ≤ blockLength) :
    ∃ tubeWidth₀ : ℝ, 0 < tubeWidth₀ ∧
      ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ upper binWidth : ℝ, ∀ pattern : Finset (Fin q),
        (iidSequenceLaw ν).real
          (drawdownConditionalBlockIntersection
            (drawdownJumpPatternTubeEvent remainder blockLength pattern
              upper binWidth tubeWidth) q) ≤
          ∏ j ∈ Finset.range q,
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ v -
                d * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
  obtain ⟨tubeWidth₀, htubeWidth₀, hblockBound⟩ :=
    iidSequenceLaw_condExp_drawdownTubeBlockEvent_le_of_finiteVariance
      ν hν hsquare hvariance hv hd hcritical
  refine ⟨tubeWidth₀, htubeWidth₀, ?_⟩
  intro tubeWidth htubeWidth upper binWidth pattern
  exact measureReal_drawdownJumpPatternTubeIntersection_le_prod_of_uniformBlockBound
    ν hblockBound remainder q blockLength hblockLength
    tubeWidth htubeWidth upper binWidth pattern

/-- The tube condition for block `j` in the proof of Wang Yiyang, Chapter 3,
Lemma 3.3. Its interval is centered at the discretized running maximum at
the block's starting time. -/
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
theorem drawdownBlockTubeCondition_implies_tubeBlockEvent
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
theorem drawdown_card_maximumJumpSet_le {q K : ℕ}
    (bins : Fin (q + 1) → Fin (K + 1))
    (hmono : ∀ i j, i ≤ j → bins j ≤ bins i) :
    (drawdownMaximumJumpSet bins).card ≤ K + 1 := by
  exact card_spatialBinJumpSet_le bins hmono

/-- On the event in Wang Yiyang, Chapter 3, Lemma 3.3, the running maximum
can be rounded to a nondecreasing sequence of finitely many levels. Every
block with unchanged level is contained in the interval
`(M_j - width - delta, M_j]`.

The sequence is encoded by its grid indices, so `hmono` states that the
indices are nonincreasing. The last component is the tube inclusion used in
the conditional-expectation step of Wang Yiyang, *Asymptotic speed of the
$N$-branching random walk with infinite offspring*, Chapter 3, Lemma 3.3. -/
theorem drawdown_discretizedMaximumBlockDecomposition
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
theorem additivePath_le_threshold_add_delta_of_noLargeDrop
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
theorem neg_delta_le_additivePath_of_noLargeDrop
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

/-- An oscillation bound for the additive path over one segment is exactly
the finite-block oscillation event for its increments. -/
theorem blockOscillationEvent_of_additiveSegment
    {start length : ℕ} {increment : ℕ → ℝ} {width : ℝ}
    (hsegment : OscillationBounded
      (fun k : Fin (length + 1) =>
        AdditivePath.displacement (start + (k : ℕ)) increment) width) :
    blockOscillationEvent width length
      (Combinatorics.Sequence.blockCoordinates start length increment) := by
  change OscillationBounded
    (fun k : Fin (length + 1) =>
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates start length increment) k)
    width
  intro i j
  change |Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) i -
    Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) j| ≤ width
  have hpartial (k : Fin (length + 1)) :
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates start length increment) k =
        AdditivePath.displacement (start + (k : ℕ)) increment -
          AdditivePath.displacement start increment := by
    rw [partialSum_blockCoordinates, AdditivePath.displacement_add_eq_add_blockSum]
    ring
  rw [hpartial i, hpartial j]
  calc
    |(AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement start increment) -
      (AdditivePath.displacement (start + (j : ℕ)) increment -
          AdditivePath.displacement start increment)| =
        |AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement (start + (j : ℕ)) increment| := by
      congr 1
      ring
    _ ≤ width := hsegment i j

/-- A finite-horizon event imposing both a drawdown bound and an endpoint
upper bound. -/
def noLargeDropEndpointBelowEvent (horizon : ℕ) (delta threshold : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | (∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta) ∧
    AdditivePath.displacement horizon increment ≤ threshold}

/-- Every path in `noLargeDropEndpointBelowEvent` has the discretized
running-maximum decomposition of Wang Yiyang, Chapter 3, Lemma 3.3. The
endpoint condition supplies the deterministic ceiling `threshold + delta`;
the drawdown condition supplies the lower side of each unchanged-maximum
block interval. -/
theorem drawdown_event_discretizedMaximumBlockDecomposition
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
Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, Lemma 3.3. This packages the deterministic reduction
preceding its conditional-expectation iteration. -/
theorem drawdown_event_goodBlocks_satisfy_tubeCondition
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
  drawdownConditionalBlockIntersection
    (drawdownJumpPatternTubeEvent remainder blockLength pattern
      upper binWidth tubeWidth) q

/-- The finite family of jump patterns with at most `K` jump indices. -/
noncomputable def drawdownAdmissibleJumpPatterns (q K : ℕ) :
    Finset (Finset (Fin q)) :=
  Finset.univ.filter fun pattern => pattern.card ≤ K

/-- If the pattern is the actual jump set of the rounded running maximum,
every block tube required by that pattern holds whenever its deterministic
good-block condition holds. -/
theorem drawdown_mem_jumpPatternTubeIntersection_of_goodBlocks
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
      increment ∈ drawdownConditionalBlockIntersection events n := by
    intro n hn
    induction n with
    | zero => simp [drawdownConditionalBlockIntersection]
    | succ n ih =>
        rw [drawdownConditionalBlockIntersection]
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
decomposition in Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Chapter 3, proof of Lemma 3.3. -/
theorem drawdown_noLargeDropEvent_subset_jumpPatternUnion
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

private theorem measureReal_noLargeDropEvent_le_sum_jumpPatternProducts_of_uniformBlockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {v d tubeWidth₀ : ℝ}
    (horizon blockLength : ℕ)
    (hpatternBound : ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ upper binWidth : ℝ, ∀ pattern : Finset (Fin (horizon / blockLength)),
        (iidSequenceLaw ν).real
          (drawdownConditionalBlockIntersection
            (drawdownJumpPatternTubeEvent (horizon % blockLength) blockLength pattern
              upper binWidth tubeWidth) (horizon / blockLength)) ≤
          ∏ j ∈ Finset.range (horizon / blockLength),
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ v -
                d * ((blockLength : ℝ) / tubeWidth ^ 2))) j)
    (delta threshold binWidth : ℝ) (hbinWidth : 0 < binWidth)
    (htubeWidth : tubeWidth₀ ≤ binWidth + delta) :
      (iidSequenceLaw ν).real
        (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
        ∑ pattern ∈ drawdownAdmissibleJumpPatterns
            (horizon / blockLength)
            (⌊(threshold + delta) / binWidth⌋₊ + 1),
          ∏ j ∈ Finset.range (horizon / blockLength),
            drawdownJumpPatternBound pattern
              (Real.exp ((binWidth + delta) ^ v -
                d * ((blockLength : ℝ) / (binWidth + delta) ^ 2))) j := by
  let tubeWidth := binWidth + delta
  let q := horizon / blockLength
  let maxJumps := ⌊(threshold + delta) / binWidth⌋₊ + 1
  let patterns := drawdownAdmissibleJumpPatterns q maxJumps
  let events : Finset (Fin q) → Set (ℕ → ℝ) := fun pattern =>
    drawdownJumpPatternTubeIntersection (horizon % blockLength) blockLength
      pattern (threshold + delta) binWidth tubeWidth
  have hsubset : noLargeDropEndpointBelowEvent horizon delta threshold ⊆
      ⋃ pattern ∈ patterns, events pattern := by
    intro increment hevent
    have hmem := drawdown_noLargeDropEvent_subset_jumpPatternUnion
      increment horizon blockLength delta threshold binWidth hbinWidth hevent
    simpa [q, maxJumps, patterns, events] using hmem
  have hbound : ∀ pattern ∈ patterns,
      (iidSequenceLaw ν).real (events pattern) ≤
        ∏ j ∈ Finset.range q,
          drawdownJumpPatternBound pattern
            (Real.exp (tubeWidth ^ v -
              d * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
    intro pattern hpattern
    simpa [events, q, drawdownJumpPatternTubeIntersection] using
      hpatternBound tubeWidth htubeWidth (threshold + delta) binWidth pattern
  have hfiniteUnion : (iidSequenceLaw ν) (⋃ pattern ∈ patterns, events pattern) ≠ ∞ :=
    measure_ne_top (iidSequenceLaw ν) _
  calc
    (iidSequenceLaw ν).real
        (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
        (iidSequenceLaw ν).real (⋃ pattern ∈ patterns, events pattern) :=
      measureReal_mono hsubset hfiniteUnion
    _ ≤ ∑ pattern ∈ patterns, (iidSequenceLaw ν).real (events pattern) :=
      measureReal_biUnion_finset_le patterns events
    _ ≤ ∑ pattern ∈ patterns,
          ∏ j ∈ Finset.range q,
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ v -
                d * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
      exact Finset.sum_le_sum hbound

/-- The probability of the drawdown event is bounded by the sum of the
conditional-expectation products over all admissible rounded-maximum jump
patterns. This is the finite-horizon estimate obtained by the Markov
iteration in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Chapter 3, proof of Lemma 3.3. -/
theorem measureReal_noLargeDropEvent_le_sum_jumpPatternProducts
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance)
    (horizon blockLength : ℕ) (hblockLength : 1 ≤ blockLength)
    (delta threshold binWidth : ℝ) (hbinWidth : 0 < binWidth) :
    ∃ tubeWidth₀ : ℝ, 0 < tubeWidth₀ ∧
      (tubeWidth₀ ≤ binWidth + delta →
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
          ∑ pattern ∈ drawdownAdmissibleJumpPatterns
              (horizon / blockLength)
              (⌊(threshold + delta) / binWidth⌋₊ + 1),
            ∏ j ∈ Finset.range (horizon / blockLength),
              drawdownJumpPatternBound pattern
                (Real.exp ((binWidth + delta) ^ v -
                  d * ((blockLength : ℝ) / (binWidth + delta) ^ 2))) j) := by
  obtain ⟨tubeWidth₀, htubeWidth₀, hpatternBound⟩ :=
    measureReal_drawdownJumpPatternTubeIntersection_le_prod
      ν hν hsquare hvariance hv hd hcritical
      (horizon % blockLength) (horizon / blockLength) blockLength hblockLength
  refine ⟨tubeWidth₀, htubeWidth₀, ?_⟩
  intro htubeWidth
  simpa using measureReal_noLargeDropEvent_le_sum_jumpPatternProducts_of_uniformBlockBound
    ν horizon blockLength hpatternBound
    delta threshold binWidth hbinWidth htubeWidth

/-- Counting the admissible jump patterns and using at least `q-K` nonjump
blocks gives the exponential-count times one-block-power estimate from the
proof of Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Chapter 3, Lemma 3.3. -/
private theorem measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow_of_sumBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {v d : ℝ}
    (horizon blockLength : ℕ)
    (delta threshold binWidth : ℝ)
    (hsum : (iidSequenceLaw ν).real
      (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
      ∑ pattern ∈ drawdownAdmissibleJumpPatterns
          (horizon / blockLength)
          (⌊(threshold + delta) / binWidth⌋₊ + 1),
        ∏ j ∈ Finset.range (horizon / blockLength),
          drawdownJumpPatternBound pattern
            (Real.exp ((binWidth + delta) ^ v -
              d * ((blockLength : ℝ) / (binWidth + delta) ^ 2))) j)
    (hp : Real.exp ((binWidth + delta) ^ v -
      d * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ≤ 1) :
    (iidSequenceLaw ν).real
        (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
      (2 : ℝ) ^ (horizon / blockLength) *
        Real.exp ((binWidth + delta) ^ v -
          d * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ^
            (horizon / blockLength -
              (⌊(threshold + delta) / binWidth⌋₊ + 1)) := by
  let q := horizon / blockLength
  let maxJumps := ⌊(threshold + delta) / binWidth⌋₊ + 1
  let patterns := drawdownAdmissibleJumpPatterns q maxJumps
  let p := Real.exp ((binWidth + delta) ^ v -
    d * ((blockLength : ℝ) / (binWidth + delta) ^ 2))
  have hpatternProduct : ∀ pattern ∈ patterns,
      (∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
        p ^ (q - maxJumps) := by
    intro pattern hpattern
    have hcard : pattern.card ≤ maxJumps := by
      simpa [patterns, drawdownAdmissibleJumpPatterns, q, maxJumps] using hpattern
    exact drawdown_prod_jumpPatternBound_le_pow pattern p
      (Real.exp_nonneg _) hp hcard
  have hsum' : (iidSequenceLaw ν).real
      (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
      ∑ pattern ∈ patterns,
        ∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j := by
    simpa [q, maxJumps, patterns, p] using hsum
  have hcardPatterns : patterns.card ≤ 2 ^ q := by
    calc
      patterns.card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ q := by simp [q]
  have hsumPow :
      (∑ pattern ∈ patterns,
        ∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
          (patterns.card : ℝ) * p ^ (q - maxJumps) := by
    calc
      (∑ pattern ∈ patterns,
          ∏ j ∈ Finset.range q, drawdownJumpPatternBound pattern p j) ≤
          ∑ pattern ∈ patterns, p ^ (q - maxJumps) :=
        Finset.sum_le_sum hpatternProduct
      _ = (patterns.card : ℝ) * p ^ (q - maxJumps) := by simp
  have hcount : (patterns.card : ℝ) ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hcardPatterns
  have hpowerNonneg : 0 ≤ p ^ (q - maxJumps) :=
    pow_nonneg (Real.exp_nonneg _) _
  have hfinal := hsum'.trans hsumPow
  have hfinal' := hfinal.trans
    (mul_le_mul_of_nonneg_right hcount hpowerNonneg)
  simpa [q, maxJumps, p, mul_comm] using hfinal'

theorem measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance)
    (horizon blockLength : ℕ) (hblockLength : 1 ≤ blockLength)
    (delta threshold binWidth : ℝ) (hbinWidth : 0 < binWidth) :
    ∃ tubeWidth₀ : ℝ, 0 < tubeWidth₀ ∧
      (tubeWidth₀ ≤ binWidth + delta →
        Real.exp ((binWidth + delta) ^ v -
          d * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ≤ 1 →
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
          (2 : ℝ) ^ (horizon / blockLength) *
            Real.exp ((binWidth + delta) ^ v -
              d * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ^
                (horizon / blockLength -
                  (⌊(threshold + delta) / binWidth⌋₊ + 1))) := by
  obtain ⟨tubeWidth₀, htubeWidth₀, hsum⟩ :=
    measureReal_noLargeDropEvent_le_sum_jumpPatternProducts
      ν hν hsquare hvariance hv hd hcritical horizon blockLength hblockLength
      delta threshold binWidth hbinWidth
  refine ⟨tubeWidth₀, htubeWidth₀, ?_⟩
  intro htubeWidth hp
  exact measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow_of_sumBound
    ν horizon blockLength delta threshold binWidth (hsum htubeWidth) hp

private theorem exp_pow_nat (x : ℝ) (n : ℕ) :
    Real.exp x ^ n = Real.exp ((n : ℝ) * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        Real.exp x ^ (n + 1) = Real.exp x ^ n * Real.exp x := by
          rw [pow_succ]
        _ = Real.exp ((n : ℝ) * x) * Real.exp x := by rw [ih]
        _ = Real.exp ((n : ℝ) * x + x) := by rw [← Real.exp_add]
        _ = Real.exp (((n : ℝ) + 1) * x) := by
          congr 1
          ring
        _ = Real.exp (((n + 1 : ℕ) : ℝ) * x) := by
          congr 1
          rw [Nat.cast_succ]

private theorem jumpPatternProbability_le_exp
    {q K : ℕ} {z t eta d : ℝ}
    (hz : 0 ≤ z) (ht : 0 < t) (heta : 0 < eta) (hd : 0 < d)
    (hqLower : z / t - 1 ≤ (q : ℝ))
    (hqUpper : (q : ℝ) ≤ z / Real.sqrt t)
    (hqK : K ≤ q)
    (hentropy : Real.log 2 / Real.sqrt t ≤ d * eta)
    (hjump : d * (1 + 2 * eta) * t * ((K : ℝ) + 1) ≤ d * eta * z) :
    (2 : ℝ) ^ q * Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) ≤
      Real.exp (-d * z) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqEntropy : (q : ℝ) * Real.log 2 ≤ d * eta * z := by
    calc
      (q : ℝ) * Real.log 2 ≤ (z / Real.sqrt t) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hqUpper hlog2.le
      _ = (Real.log 2 / Real.sqrt t) * z := by ring
      _ ≤ d * eta * z := mul_le_mul_of_nonneg_right hentropy hz
  have hqSub : ((q - K : ℕ) : ℝ) = (q : ℝ) - (K : ℝ) := by
    rw [Nat.cast_sub hqK]
  have hcoef : 0 < d * (1 + 2 * eta) * t := by positivity
  have hqLowerMul :
      -(d * (1 + 2 * eta) * t) * (q : ℝ) ≤
        -(d * (1 + 2 * eta) * t) * (z / t - 1) :=
    mul_le_mul_of_nonpos_left hqLower (neg_nonpos.mpr hcoef.le)
  have hnegative :
      -(d * (1 + 2 * eta) * t) * ((q - K : ℕ) : ℝ) ≤
        -d * (1 + 2 * eta) * z +
          d * (1 + 2 * eta) * t * ((K : ℝ) + 1) := by
    rw [hqSub]
    calc
      -(d * (1 + 2 * eta) * t) * ((q : ℝ) - (K : ℝ)) =
          -(d * (1 + 2 * eta) * t) * (q : ℝ) +
            d * (1 + 2 * eta) * t * (K : ℝ) := by ring
      _ ≤ -(d * (1 + 2 * eta) * t) * (z / t - 1) +
            d * (1 + 2 * eta) * t * (K : ℝ) :=
        by nlinarith [hqLowerMul]
      _ = -d * (1 + 2 * eta) * z +
            d * (1 + 2 * eta) * t * ((K : ℝ) + 1) := by
        field_simp [ht.ne']
        ring
  have hexponent :
      (q : ℝ) * Real.log 2 -
        d * (1 + 2 * eta) * t * ((q - K : ℕ) : ℝ) ≤ -d * z := by
    calc
      (q : ℝ) * Real.log 2 -
          d * (1 + 2 * eta) * t * ((q - K : ℕ) : ℝ) =
          (q : ℝ) * Real.log 2 +
            (-(d * (1 + 2 * eta) * t) * ((q - K : ℕ) : ℝ)) := by ring
      _ ≤ d * eta * z +
            (-d * (1 + 2 * eta) * z +
              d * (1 + 2 * eta) * t * ((K : ℝ) + 1)) :=
        add_le_add hqEntropy hnegative
      _ ≤ d * eta * z + (-d * (1 + 2 * eta) * z + d * eta * z) := by
        nlinarith [hjump]
      _ = -d * z := by ring
  have hpowTwo : (2 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 2) := by
    calc
      (2 : ℝ) ^ q = (Real.exp (Real.log 2)) ^ q := by
        rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((q : ℝ) * Real.log 2) := exp_pow_nat _ _
  have hpowExp :
      Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) =
        Real.exp ((-d * (1 + 2 * eta) * t) * ((q - K : ℕ) : ℝ)) := by
    convert exp_pow_nat
      (-(d * (1 + 2 * eta) * t)) (q - K) using 1 <;> ring
  calc
    (2 : ℝ) ^ q * Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) =
        Real.exp ((q : ℝ) * Real.log 2 -
          d * (1 + 2 * eta) * t * ((q - K : ℕ) : ℝ)) := by
            rw [hpowTwo, hpowExp, ← Real.exp_add]
            congr 1
            ring
    _ ≤ Real.exp (-d * z) := Real.exp_le_exp.mpr hexponent

private theorem eventually_real_rpow_ge_const
    {power bound : ℝ} (hpower : 0 < power) :
    ∀ᶠ x : ℝ in atTop, bound ≤ x ^ power := by
  exact (_root_.tendsto_rpow_atTop hpower).eventually
    (eventually_ge_atTop bound)

/-- For every positive block exponent, a floor-rounded block length remains
between the half-exponent and full-exponent powers once the width is large. -/
theorem eventually_drawdownFloorBlockLength_bounds
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ Delta : ℝ in atTop,
      1 ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
      Delta ^ (2 + eta) - Delta ^ (2 + eta / 2) ≤
        (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
      Delta ^ (2 + eta / 2) ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
      (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ≤ Delta ^ (2 + eta) := by
  have hlargePower := eventually_real_rpow_ge_const
    (power := 2 + eta / 2) (bound := 1) (by linarith)
  have hlargeFactor := eventually_real_rpow_ge_const
    (power := eta / 2) (bound := 2) (by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlargePower, hlargeFactor] with
    Delta hDelta hlarge hfactor
  have hDeltaPos : 0 < Delta := by linarith
  have hbaseNonneg : 0 ≤ Delta ^ (2 + eta) := by positivity
  have hfloorUpper : (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ≤ Delta ^ (2 + eta) :=
    Nat.floor_le hbaseNonneg
  have hfloorLower : Delta ^ (2 + eta) - 1 <
      (⌊Delta ^ (2 + eta)⌋₊ : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (Delta ^ (2 + eta))
    have hfloorReal : Delta ^ (2 + eta) <
        (⌊Delta ^ (2 + eta)⌋₊ : ℝ) + 1 := by exact_mod_cast hfloor
    linarith
  have hpowerOrder : Delta ^ (2 + eta / 2) ≤ Delta ^ (2 + eta) :=
    Real.rpow_le_rpow_of_exponent_le hDelta (by linarith)
  have hpowerSplit : Delta ^ (2 + eta) =
      Delta ^ (2 + eta / 2) * Delta ^ (eta / 2) := by
    rw [← Real.rpow_add hDeltaPos (2 + eta / 2) (eta / 2)]
    congr 1
    ring
  have hpowerGap : 1 ≤ Delta ^ (2 + eta) - Delta ^ (2 + eta / 2) := by
    rw [hpowerSplit]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlarge) (sub_nonneg.mpr hfactor)]
  have hhalfPowerLower : Delta ^ (2 + eta / 2) ≤
      Delta ^ (2 + eta) - 1 := by linarith
  have hhalfPowerFloor : Delta ^ (2 + eta / 2) ≤
      (⌊Delta ^ (2 + eta)⌋₊ : ℝ) := by
    exact hhalfPowerLower.trans hfloorLower.le
  have hfloorPos : 1 ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) := by
    have hnat : 1 ≤ ⌊Delta ^ (2 + eta)⌋₊ := by
      rw [Nat.one_le_floor_iff]
      exact hlarge.trans hpowerOrder
    exact_mod_cast hnat
  refine ⟨?_, ?_, hhalfPowerFloor, hfloorUpper⟩
  · exact hfloorPos
  · nlinarith [hlarge, hfloorLower]

private theorem eventually_drawdownCeilingBinWidth_bounds
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ Delta : ℝ in atTop,
      1 ≤ Delta ∧
      Delta + (⌈eta * Delta⌉₊ : ℝ) ≤ (1 + 2 * eta) * Delta := by
  filter_upwards [eventually_ge_atTop (1 / eta : ℝ),
      eventually_ge_atTop (1 : ℝ)] with Delta hDeltaEta hDelta
  have hDeltaPos : 0 < Delta := by linarith
  have hEtaDelta : 1 ≤ eta * Delta := by
    have h := (div_le_iff₀ heta).mp hDeltaEta
    nlinarith [h]
  have hceilLower : eta * Delta ≤ (⌈eta * Delta⌉₊ : ℝ) := by
    exact_mod_cast (Nat.le_ceil (eta * Delta))
  have hceilUpper : (⌈eta * Delta⌉₊ : ℝ) < eta * Delta + 1 := by
    exact_mod_cast (Nat.ceil_lt_add_one (mul_nonneg heta.le hDeltaPos.le))
  refine ⟨hDelta, ?_⟩
  calc
    Delta + (⌈eta * Delta⌉₊ : ℝ) ≤ Delta + (eta * Delta + 1) := by
      linarith
    _ ≤ Delta + 2 * eta * Delta := by nlinarith
    _ = (1 + 2 * eta) * Delta := by ring

private theorem eventually_drawdownTubeBlockExponent_le
    {eta d : ℝ} (heta : 0 < eta) (hd : 0 < d) :
    ∀ᶠ Delta : ℝ in atTop,
      (⌈eta * Delta⌉₊ + Delta) ^ (eta / 2) -
        d * (1 + 2 * eta) ^ 4 *
          ((⌊Delta ^ (2 + eta)⌋₊ : ℝ) /
            (⌈eta * Delta⌉₊ + Delta) ^ 2) ≤
        -d * (1 + 2 * eta) * Delta ^ eta := by
  let B : ℝ := 1 + 2 * eta
  let A : ℝ := B ^ (eta / 2) + d * B ^ 2
  let R : ℝ := 2 * d * eta * B
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hgrowth := eventually_real_rpow_ge_const
    (power := eta / 2) (bound := A / R) (by linarith)
  filter_upwards [eventually_drawdownFloorBlockLength_bounds heta,
      eventually_drawdownCeilingBinWidth_bounds heta, hgrowth] with
      Delta hfloor hceil hgrowth
  have hDelta : 1 ≤ Delta := hceil.1
  have hDeltaPos : 0 < Delta := by linarith
  let width : ℝ := (⌈eta * Delta⌉₊ : ℝ) + Delta
  let length : ℝ := (⌊Delta ^ (2 + eta)⌋₊ : ℝ)
  let g : ℝ := Delta ^ (eta / 2)
  let a : ℝ := Delta ^ eta
  have hwidthPos : 0 < width := by dsimp [width]; positivity
  have hwidthUpper : width ≤ B * Delta := by
    dsimp [width, B]
    simpa [add_comm] using hceil.2
  have hwidthPow : width ^ (eta / 2) ≤ B ^ (eta / 2) * g := by
    calc
      width ^ (eta / 2) ≤ (B * Delta) ^ (eta / 2) := by
        apply Real.rpow_le_rpow (le_of_lt hwidthPos) hwidthUpper
        linarith
      _ = B ^ (eta / 2) * g := by
        rw [Real.mul_rpow hB.le hDeltaPos.le]
  have hpowerEta : Delta ^ (2 + eta) = Delta ^ 2 * a := by
    simpa [a, Real.rpow_natCast] using
      (Real.rpow_add hDeltaPos (2 : ℝ) eta)
  have hpowerEtaHalf : Delta ^ (2 + eta / 2) = Delta ^ 2 * g := by
    simpa [g, Real.rpow_natCast] using
      (Real.rpow_add hDeltaPos (2 : ℝ) (eta / 2))
  have hpowOrder : g ≤ a := by
    dsimp [g, a]
    exact Real.rpow_le_rpow_of_exponent_le hDelta (by linarith)
  have hlengthLower : Delta ^ 2 * (a - g) ≤ length := by
    calc
      Delta ^ 2 * (a - g) = Delta ^ (2 + eta) - Delta ^ (2 + eta / 2) := by
        rw [hpowerEta, hpowerEtaHalf]
        ring
      _ ≤ length := by simpa [length] using hfloor.2.1
  have hnumNonneg : 0 ≤ Delta ^ 2 * (a - g) := by
    exact mul_nonneg (sq_nonneg Delta) (sub_nonneg.mpr hpowOrder)
  have hwidthUpperSq : width ^ 2 ≤ (B * Delta) ^ 2 := by
    exact (sq_le_sq₀ (le_of_lt hwidthPos) (mul_nonneg hB.le hDeltaPos.le)).2
      hwidthUpper
  have hwidthSqPos : 0 < width ^ 2 := sq_pos_of_pos hwidthPos
  have hupperSqPos : 0 < (B * Delta) ^ 2 :=
    sq_pos_of_pos (mul_pos hB hDeltaPos)
  have hinv : ((B * Delta) ^ 2)⁻¹ ≤ (width ^ 2)⁻¹ :=
    (inv_le_inv₀ hupperSqPos hwidthSqPos).2 hwidthUpperSq
  have hfrac : (a - g) / B ^ 2 ≤ length / width ^ 2 := by
    have hfrac' :
        Delta ^ 2 * (a - g) / (B * Delta) ^ 2 ≤ length / width ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        Delta ^ 2 * (a - g) * ((B * Delta) ^ 2)⁻¹ ≤
            Delta ^ 2 * (a - g) * (width ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hnumNonneg
        _ ≤ length * (width ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hlengthLower
                (inv_nonneg.mpr (le_of_lt hwidthSqPos))
    have hcancel :
        Delta ^ 2 * (a - g) / (B * Delta) ^ 2 = (a - g) / B ^ 2 := by
      field_simp [ne_of_gt hDeltaPos, ne_of_gt hB]
    rw [hcancel] at hfrac'
    exact hfrac'
  have hpenalty : d * B ^ 2 * (a - g) ≤
      d * B ^ 4 * (length / width ^ 2) := by
    calc
      d * B ^ 2 * (a - g) = d * B ^ 4 * ((a - g) / B ^ 2) := by
        field_simp [ne_of_gt hB]
      _ ≤ d * B ^ 4 * (length / width ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
  have hdominance : A ≤ R * g := by
    have h := mul_le_mul_of_nonneg_left hgrowth hR.le
    calc
      A = R * (A / R) := by field_simp [ne_of_gt hR]
      _ ≤ R * g := h
  have hdominanceMul : A * g ≤ R * g ^ 2 := by
    calc
      A * g ≤ (R * g) * g :=
        mul_le_mul_of_nonneg_right hdominance (show 0 ≤ g by positivity)
      _ = R * g ^ 2 := by ring
  have hgsq : g ^ 2 = a := by
    dsimp [g, a]
    rw [← Real.rpow_natCast (Delta ^ (eta / 2)) 2,
      ← Real.rpow_mul hDeltaPos.le]
    congr 1
    ring
  have hexponent : width ^ (eta / 2) -
      d * B ^ 4 * (length / width ^ 2) ≤ -d * B * a := by
    dsimp [A, R] at hdominanceMul
    rw [hgsq] at hdominanceMul
    nlinarith [hwidthPow, hpenalty, hdominanceMul]
  simpa [width, length, a, B] using hexponent

private theorem drawdownBlockCount_scaledBounds
    {Delta eta : ℝ} {horizon blockLength : ℕ}
    (hDelta : 0 < Delta)
    (hblockLength : 1 ≤ blockLength)
    (hblockLengthLower : Delta ^ (2 + eta / 2) ≤ (blockLength : ℝ))
    (hblockLengthUpper : (blockLength : ℝ) ≤ Delta ^ (2 + eta)) :
    ((horizon : ℝ) / Delta ^ 2) / Delta ^ eta - 1 ≤
        ((horizon / blockLength : ℕ) : ℝ) ∧
      ((horizon / blockLength : ℕ) : ℝ) ≤
        ((horizon : ℝ) / Delta ^ 2) / Real.sqrt (Delta ^ eta) := by
  let q : ℕ := horizon / blockLength
  let qReal : ℝ := (q : ℝ)
  have hblockLengthPos : 0 < (blockLength : ℝ) := by
    exact_mod_cast (show 0 < blockLength by omega)
  have hscaleDenom : Delta ^ (2 + eta) = Delta ^ 2 * Delta ^ eta := by
    simpa [Real.rpow_natCast] using (Real.rpow_add hDelta (2 : ℝ) eta)
  have hscaleDenomHalf : Delta ^ (2 + eta / 2) =
      Delta ^ 2 * Delta ^ (eta / 2) := by
    simpa [Real.rpow_natCast] using (Real.rpow_add hDelta (2 : ℝ) (eta / 2))
  have hsqrt : Real.sqrt (Delta ^ eta) = Delta ^ (eta / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hDelta.le]
    congr 1
    ring
  have hNatDivUpper : q * blockLength ≤ horizon := by
    dsimp [q]
    exact Nat.div_mul_le_self _ _
  have hNatDivLower : horizon < (q + 1) * blockLength := by
    apply (Nat.div_lt_iff_lt_mul hblockLength).mp
    dsimp [q]
    exact Nat.lt_succ_self _
  have hqUpper : qReal ≤ (horizon : ℝ) / Delta ^ (2 + eta / 2) := by
    have hmul : qReal * Delta ^ (2 + eta / 2) ≤ (horizon : ℝ) := by
      calc
        qReal * Delta ^ (2 + eta / 2) ≤ qReal * (blockLength : ℝ) :=
          mul_le_mul_of_nonneg_left hblockLengthLower (by positivity)
        _ ≤ (horizon : ℝ) := by
          change (q : ℝ) * (blockLength : ℝ) ≤ (horizon : ℝ)
          exact_mod_cast hNatDivUpper
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hDelta (2 + eta / 2))).2 hmul
  have hqLower : (horizon : ℝ) / Delta ^ (2 + eta) < qReal + 1 := by
    have hmul : (horizon : ℝ) < (qReal + 1) * Delta ^ (2 + eta) := by
      calc
        (horizon : ℝ) < ((q + 1) * blockLength : ℕ) := by exact_mod_cast hNatDivLower
        _ ≤ (qReal + 1) * Delta ^ (2 + eta) := by
          calc
            ((q + 1) * blockLength : ℕ) =
                ((q + 1 : ℕ) : ℝ) * (blockLength : ℝ) := by norm_num
            _ ≤ ((q + 1 : ℕ) : ℝ) * Delta ^ (2 + eta) :=
              mul_le_mul_of_nonneg_left hblockLengthUpper (by positivity)
            _ = (qReal + 1) * Delta ^ (2 + eta) := by simp [qReal]
    exact (div_lt_iff₀ (Real.rpow_pos_of_pos hDelta (2 + eta))).2 hmul
  have hqLowerScaled :
      ((horizon : ℝ) / Delta ^ 2) / Delta ^ eta - 1 < qReal := by
    have hratio : ((horizon : ℝ) / Delta ^ 2) / Delta ^ eta =
        (horizon : ℝ) / Delta ^ (2 + eta) := by
      rw [div_div, hscaleDenom]
    rw [hratio]
    linarith
  have hqUpperScaled :
      qReal ≤ ((horizon : ℝ) / Delta ^ 2) / Real.sqrt (Delta ^ eta) := by
    have hratio : (horizon : ℝ) / Delta ^ (2 + eta / 2) =
        ((horizon : ℝ) / Delta ^ 2) / Real.sqrt (Delta ^ eta) := by
      rw [div_div, hsqrt, hscaleDenomHalf]
    rw [← hratio]
    exact hqUpper
  constructor
  · exact le_of_lt (by simpa [q, qReal] using hqLowerScaled)
  · simpa [q, qReal] using hqUpperScaled

private theorem drawdownJumpCount_add_one_le
    {Delta c eta : ℝ}
    (hDelta : 1 ≤ Delta) (hc : 0 < c)
    (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    ((⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ + 1 : ℕ) : ℝ) + 1 ≤
      2 * (1 / c + 2) / eta := by
  have hDeltaPos : 0 < Delta := by linarith
  have hbinLower : eta * Delta ≤ (⌈eta * Delta⌉₊ : ℝ) := by
    exact_mod_cast Nat.le_ceil (eta * Delta)
  have hbinPos : 0 < (⌈eta * Delta⌉₊ : ℝ) :=
    lt_of_lt_of_le (mul_pos heta hDeltaPos) hbinLower
  have hratio : (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) ≤
      (1 / c + 1) / eta := by
    have hnum : Delta / c + Delta = (1 / c + 1) * Delta := by ring
    have hfirst :
        (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) ≤
          (Delta / c + Delta) / (eta * Delta) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos heta hDeltaPos) hbinLower
    have hsecond : (Delta / c + Delta) / (eta * Delta) =
        (1 / c + 1) / eta := by rw [hnum]; field_simp [ne_of_gt heta, ne_of_gt hDeltaPos]
    exact hfirst.trans_eq hsecond
  have hratioNonneg : 0 ≤ (Delta / c + Delta) /
      (⌈eta * Delta⌉₊ : ℝ) := by positivity
  have hfloor :
      (⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ : ℝ) ≤
        (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) :=
    Nat.floor_le hratioNonneg
  have hconstant : (1 / c + 1) / eta + 2 ≤ 2 * (1 / c + 2) / eta := by
    have hc' : 0 < 1 / c := by positivity
    field_simp [ne_of_gt hc, ne_of_gt heta]
    nlinarith [hetaLeOne]
  have hcast :
      ((⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ + 1 : ℕ) : ℝ) + 1 =
        (⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ : ℝ) + 2 := by
    norm_num
    ring
  rw [hcast]
  calc
    (⌊(Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ)⌋₊ : ℝ) + 2 ≤
        (Delta / c + Delta) / (⌈eta * Delta⌉₊ : ℝ) + 2 := by linarith
    _ ≤ (1 / c + 1) / eta + 2 := by linarith
    _ ≤ 2 * (1 / c + 2) / eta := hconstant

/-- The final entropy and jump-count estimates in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.3, turn the finite jump-pattern bound into the
desired exponential rate. Here `z = L / Δ^2`, `t = Δ^η`, and `K` bounds the
number of jumps. The one-block rate is assumed in the explicit form
\[
  (w+\Delta)^v-d_0\frac{\ell}{(w+\Delta)^2}
    \le -d(1+2\eta)t.
\] -/
theorem measureReal_noLargeDropEvent_le_exp_of_blockParameters
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance v blockRate eta target t z : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    (hv : 0 < v) (hblockRate : 0 < blockRate)
    (hcritical : blockRate < (Real.pi ^ 2 / 2) * variance)
    (heta : 0 < eta) (ht : 0 < t) (htarget : 0 < target)
    (hz : 0 ≤ z)
    (horizon blockLength : ℕ) (hblockLength : 1 ≤ blockLength)
    (delta threshold binWidth : ℝ) (hbinWidth : 0 < binWidth)
    (honeBlock : (binWidth + delta) ^ v -
        blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2) ≤
          -target * (1 + 2 * eta) * t)
    (hqLower : z / t - 1 ≤ ((horizon / blockLength : ℕ) : ℝ))
    (hqUpper : ((horizon / blockLength : ℕ) : ℝ) ≤ z / Real.sqrt t)
    (hmaxJumps :
      ⌊(threshold + delta) / binWidth⌋₊ + 1 ≤ horizon / blockLength)
    (hentropy : Real.log 2 / Real.sqrt t ≤ target * eta)
    (hjump : target * (1 + 2 * eta) * t *
        (((⌊(threshold + delta) / binWidth⌋₊ + 1 : ℕ) : ℝ) + 1) ≤
      target * eta * z) :
    ∃ width₀, 0 < width₀ ∧
      (width₀ ≤ binWidth + delta →
        (iidSequenceLaw ν).real
            (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
          Real.exp (-target * z)) := by
  obtain ⟨width₀, hwidth₀pos, hfinite⟩ :=
    measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow
      ν hν hsquare hvariance hv hblockRate hcritical
      horizon blockLength hblockLength delta threshold binWidth hbinWidth
  refine ⟨width₀, hwidth₀pos, ?_⟩
  intro hwidth
  have hexponentNonpos :
      (binWidth + delta) ^ v -
        blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2) ≤ 0 := by
    calc
      (binWidth + delta) ^ v -
          blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2) ≤
          -target * (1 + 2 * eta) * t := honeBlock
      _ ≤ 0 := by
        have hpositive : 0 ≤ target * (1 + 2 * eta) * t := by positivity
        nlinarith
  have hp : Real.exp ((binWidth + delta) ^ v -
      blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr hexponentNonpos
  have hfiniteBound := hfinite hwidth hp
  let q : ℕ := horizon / blockLength
  let K : ℕ := ⌊(threshold + delta) / binWidth⌋₊ + 1
  let p : ℝ := Real.exp ((binWidth + delta) ^ v -
      blockRate * ((blockLength : ℝ) / (binWidth + delta) ^ 2))
  have hqK : K ≤ q := by exact hmaxJumps
  have hsmallBlock : p ≤ Real.exp (-target * (1 + 2 * eta) * t) := by
    exact Real.exp_le_exp.mpr honeBlock
  have hpow : p ^ (q - K) ≤
      Real.exp (-target * (1 + 2 * eta) * t) ^ (q - K) :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hsmallBlock _
  have hfiniteBound' :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
        (2 : ℝ) ^ q *
          Real.exp (-target * (1 + 2 * eta) * t) ^ (q - K) := by
    calc
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta threshold) ≤
          (2 : ℝ) ^ q * p ^ (q - K) := by
            simpa only [q, K, p] using hfiniteBound
      _ ≤ (2 : ℝ) ^ q *
          Real.exp (-target * (1 + 2 * eta) * t) ^ (q - K) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfinal := jumpPatternProbability_le_exp hz ht heta htarget
    (by simpa only [q] using hqLower)
    (by simpa only [q] using hqUpper)
    hqK hentropy (by simpa only [K] using hjump)
  simpa only [q, K] using hfiniteBound'.trans hfinal

private theorem exists_drawdownBlockExponent
    {variance endpointPower horizonPower d : ℝ}
    (hvariance : 0 < variance) (hendpoint : 0 < endpointPower)
    (hhorizon : 0 < horizonPower) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ eta : ℝ, 0 < eta ∧ eta < endpointPower ∧ eta < horizonPower ∧
      eta < 1 ∧ d * (1 + 2 * eta) ^ 4 < (Real.pi ^ 2 / 2) * variance := by
  let criticalRatio : ℝ := ((Real.pi ^ 2 / 2) * variance) / d
  have hratio : 1 < criticalRatio := by
    dsimp [criticalRatio]
    exact (one_lt_div hd).2 hcritical
  have hcontinuous : ContinuousAt (fun eta : ℝ => (1 + 2 * eta) ^ 4) 0 := by
    fun_prop
  have hcriticalEventually : ∀ᶠ eta : ℝ in 𝓝 0,
      (1 + 2 * eta) ^ 4 < criticalRatio :=
    hcontinuous.eventually (Iio_mem_nhds (by simpa using hratio))
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hcriticalEventually
  let bound := min radius (min endpointPower (min horizonPower 1))
  let eta := bound / 2
  have hboundPos : 0 < bound := by
    dsimp [bound]
    positivity
  have hetaPos : 0 < eta := by dsimp [eta]; linarith
  have hetaBound : eta < bound := by dsimp [eta]; linarith
  have hboundEndpoint : bound ≤ endpointPower := by
    dsimp [bound]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hboundHorizon : bound ≤ horizonPower := by
    dsimp [bound]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hboundOne : bound ≤ 1 := by
    dsimp [bound]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hetaEndpoint : eta < endpointPower := lt_of_lt_of_le hetaBound hboundEndpoint
  have hetaHorizon : eta < horizonPower := lt_of_lt_of_le hetaBound hboundHorizon
  have hetaOne : eta < 1 := lt_of_lt_of_le hetaBound hboundOne
  have hetaRadius : eta < radius :=
    lt_of_lt_of_le hetaBound (min_le_left _ _)
  have hetaBall : eta ∈ Metric.ball (0 : ℝ) radius := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hetaPos] using hetaRadius
  have hcriticalEta : (1 + 2 * eta) ^ 4 < criticalRatio := hball hetaBall
  refine ⟨eta, hetaPos, hetaEndpoint, hetaHorizon, hetaOne, ?_⟩
  calc
    d * (1 + 2 * eta) ^ 4 < d * criticalRatio :=
      mul_lt_mul_of_pos_left hcriticalEta hd
    _ = (Real.pi ^ 2 / 2) * variance := by
      dsimp [criticalRatio]
      field_simp [ne_of_gt hd]

private theorem eventually_drawdownScaleAbsorptions
    {endpointPower horizonPower eta d : ℝ}
    (hhorizon : eta < horizonPower) (heta : 0 < eta) :
    ∀ᶠ Delta : ℝ in atTop,
      2 * (1 + 2 * eta) * (1 / endpointPower + 2) / eta ^ 2 ≤
          Delta ^ (horizonPower - eta) ∧
        Real.log 2 / (d * eta) ≤ Delta ^ (eta / 2) := by
  have hjumpExponent : 0 < horizonPower - eta := by linarith
  have hjump := eventually_real_rpow_ge_const
    (power := horizonPower - eta)
    (bound := 2 * (1 + 2 * eta) * (1 / endpointPower + 2) / eta ^ 2)
    hjumpExponent
  have hentropy := eventually_real_rpow_ge_const
    (power := eta / 2) (bound := Real.log 2 / (d * eta)) (by linarith)
  filter_upwards [hjump, hentropy] with Delta hjump hentropy
  exact ⟨hjump, hentropy⟩

/-- The generalized endpoint and horizon form of Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, Lemma 3.3. That result extends Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, Lemma 2.3 (2025,
arXiv:2512.23266), to centered finite-variance increments. For endpoint scale
`Δ / endpointPower` and horizon `L ≥ Δ^(2+horizonPower)`, the event

\[
  \{Y_L\leq \Delta/\mathrm{endpointPower},\
    \min_{0\leq i\leq j\leq L}(Y_j-Y_i)\geq-\Delta\}
\]
has real probability at most `exp (-d * (L / Δ^2))` once `Δ` is large. -/
private theorem exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance endpointPower horizonPower d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance)
    (hendpoint : 0 < endpointPower) (hhorizon : 0 < horizonPower)
    (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ horizon : ℕ,
        Delta ^ (2 + horizonPower) ≤ (horizon : ℝ) →
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / endpointPower)) ≤
          Real.exp (-d * ((horizon : ℝ) / Delta ^ 2)) := by
  obtain ⟨eta, hetaPos, hetaEndpoint, hetaHorizon, hetaOne, hcriticalEta⟩ :=
    exists_drawdownBlockExponent hvariance hendpoint hhorizon hd hcritical
  let B : ℝ := 1 + 2 * eta
  let blockRate : ℝ := d * B ^ 4
  let maxJumpFactor : ℝ := 2 * (1 / endpointPower + 2) / eta
  have hblockRatePos : 0 < blockRate := by
    dsimp [blockRate, B]
    positivity
  have hblockCritical : blockRate < (Real.pi ^ 2 / 2) * variance := by
    simpa [blockRate, B] using hcriticalEta
  obtain ⟨tubeWidth₀, htubeWidth₀, hblockBound⟩ :=
    iidSequenceLaw_condExp_drawdownTubeBlockEvent_le_of_finiteVariance
      ν hν hsquare hvariance (by linarith : 0 < eta / 2)
      hblockRatePos hblockCritical
  have hscaleAbsorptions := eventually_drawdownScaleAbsorptions
    (endpointPower := endpointPower) (d := d) hetaHorizon hetaPos
  have hgood : ∀ᶠ Delta : ℝ in atTop,
      1 ≤ Delta ∧
      1 ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
      Delta ^ (2 + eta / 2) ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
      (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ≤ Delta ^ (2 + eta) ∧
      Delta + (⌈eta * Delta⌉₊ : ℝ) ≤ B * Delta ∧
      (⌈eta * Delta⌉₊ + Delta) ^ (eta / 2) -
        blockRate * ((⌊Delta ^ (2 + eta)⌋₊ : ℝ) /
          (⌈eta * Delta⌉₊ + Delta) ^ 2) ≤ -d * B * Delta ^ eta ∧
      2 * B * (1 / endpointPower + 2) / eta ^ 2 ≤
        Delta ^ (horizonPower - eta) ∧
      Real.log 2 / (d * eta) ≤ Delta ^ (eta / 2) ∧
      tubeWidth₀ ≤ Delta := by
    filter_upwards [eventually_drawdownFloorBlockLength_bounds hetaPos,
      eventually_drawdownCeilingBinWidth_bounds hetaPos,
      eventually_drawdownTubeBlockExponent_le hetaPos hd,
      hscaleAbsorptions, eventually_ge_atTop tubeWidth₀] with
      Delta hfloor hceil hexponent hscale hwidth₀
    refine ⟨hceil.1, hfloor.1, hfloor.2.2.1, hfloor.2.2.2,
      ?_, hexponent, ?_, hscale.2, hwidth₀⟩
    · simpa [B, add_comm] using hceil.2
    · simpa [B] using hscale.1
  obtain ⟨DeltaBound, hDeltaBound⟩ := Filter.eventually_atTop.1 hgood
  let Delta₀ := max 1 DeltaBound
  refine ⟨Delta₀, le_max_left _ _, ?_⟩
  intro Delta hDelta horizon hhorizon
  have hDeltaLarge : DeltaBound ≤ Delta :=
    (le_max_right _ _).trans hDelta
  obtain ⟨hDeltaOne, hlengthPos, hlengthLower, hlengthUpper, hwidthUpper,
    honeBlock, hjumpGrowth, hentropyGrowth, hwidth₀Le⟩ := hDeltaBound Delta hDeltaLarge
  have hDeltaPos : 0 < Delta := by linarith
  let blockLength : ℕ := ⌊Delta ^ (2 + eta)⌋₊
  let binWidth : ℝ := (⌈eta * Delta⌉₊ : ℝ)
  let threshold : ℝ := Delta / endpointPower
  let q : ℕ := horizon / blockLength
  let K : ℕ := ⌊(threshold + Delta) / binWidth⌋₊ + 1
  let z : ℝ := (horizon : ℝ) / Delta ^ 2
  let t : ℝ := Delta ^ eta
  have hblockLength : 1 ≤ blockLength := by
    exact_mod_cast hlengthPos
  have hblockLengthLower : Delta ^ (2 + eta / 2) ≤ (blockLength : ℝ) := by
    exact hlengthLower
  have hblockLengthUpper : (blockLength : ℝ) ≤ Delta ^ (2 + eta) := by
    exact hlengthUpper
  have hpatternBound : ∀ tubeWidth : ℝ, tubeWidth₀ ≤ tubeWidth →
      ∀ upper binWidth' : ℝ, ∀ pattern : Finset (Fin q),
        (iidSequenceLaw ν).real
          (drawdownConditionalBlockIntersection
            (drawdownJumpPatternTubeEvent (horizon % blockLength) blockLength
              pattern upper binWidth' tubeWidth) q) ≤
          ∏ j ∈ Finset.range q,
            drawdownJumpPatternBound pattern
              (Real.exp (tubeWidth ^ (eta / 2) -
                blockRate * ((blockLength : ℝ) / tubeWidth ^ 2))) j := by
    intro tubeWidth hwidth upper binWidth' pattern
    exact measureReal_drawdownJumpPatternTubeIntersection_le_prod_of_uniformBlockBound
      ν hblockBound (horizon % blockLength) q blockLength hblockLength
      tubeWidth hwidth upper binWidth' pattern
  have hbinWidthPos : 0 < binWidth := by
    dsimp [binWidth]
    exact lt_of_lt_of_le (mul_pos hetaPos hDeltaPos) (by exact_mod_cast Nat.le_ceil _)
  have hwidthThreshold : tubeWidth₀ ≤ binWidth + Delta := by
    dsimp [binWidth]
    have hbinNonneg : 0 ≤ (⌈eta * Delta⌉₊ : ℝ) := by positivity
    linarith
  have honeBlock' : (binWidth + Delta) ^ (eta / 2) -
      blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2) ≤
        -d * (1 + 2 * eta) * t := by
    simpa [binWidth, blockLength, t, B, add_comm] using honeBlock
  have hpowerHorizon : Delta ^ (2 + horizonPower) =
      Delta ^ 2 * Delta ^ horizonPower := by
    simpa [Real.rpow_natCast] using
      (Real.rpow_add hDeltaPos (2 : ℝ) horizonPower)
  have hzLower : Delta ^ horizonPower ≤ z := by
    apply (le_div_iff₀ (sq_pos_of_pos hDeltaPos)).2
    have h := hhorizon
    rw [hpowerHorizon] at h
    simpa [mul_comm] using h
  have hcounts := drawdownBlockCount_scaledBounds
    (horizon := horizon) (blockLength := blockLength) hDeltaPos
    hblockLength hblockLengthLower hblockLengthUpper
  have hqLower : z / t - 1 ≤ (q : ℝ) := by
    simpa [q, z, t] using hcounts.1
  have hqUpper : (q : ℝ) ≤ z / Real.sqrt t := by
    simpa [q, z, t] using hcounts.2
  have hpowerDifference : Delta ^ horizonPower =
      Delta ^ eta * Delta ^ (horizonPower - eta) := by
    calc
      Delta ^ horizonPower = Delta ^ (eta + (horizonPower - eta)) := by
        congr 1
        ring
      _ = Delta ^ eta * Delta ^ (horizonPower - eta) :=
        Real.rpow_add hDeltaPos eta (horizonPower - eta)
  have hratioGrowth : Delta ^ (horizonPower - eta) ≤ z / t := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hDeltaPos eta)).2
    calc
      Delta ^ (horizonPower - eta) * t = Delta ^ horizonPower := by
        rw [hpowerDifference]
        dsimp [t]
        ring
      _ ≤ z := hzLower
  have hconst : B * maxJumpFactor / eta ≤ Delta ^ (horizonPower - eta) := by
    calc
      B * maxJumpFactor / eta =
          2 * B * (1 / endpointPower + 2) / eta ^ 2 := by
            dsimp [maxJumpFactor]
            field_simp [ne_of_gt hetaPos]
      _ ≤ Delta ^ (horizonPower - eta) := by
        simpa [B] using hjumpGrowth
  have hjumpCountBound : (K : ℝ) + 1 ≤ maxJumpFactor := by
    dsimp [K, maxJumpFactor, threshold, binWidth]
    exact drawdownJumpCount_add_one_le hDeltaOne hendpoint hetaPos hetaOne.le
  have hKleq : K ≤ q := by
    have hfactor : 1 ≤ B / eta := by
      rw [one_le_div hetaPos]
      dsimp [B]
      linarith
    have hgrowth : maxJumpFactor ≤ Delta ^ (horizonPower - eta) := by
      calc
        maxJumpFactor = 1 * maxJumpFactor := by ring
        _ ≤ (B / eta) * maxJumpFactor :=
          mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ = B * maxJumpFactor / eta := by ring
        _ ≤ Delta ^ (horizonPower - eta) := hconst
    have hKreal : (K : ℝ) ≤ (q : ℝ) := by
      nlinarith [hjumpCountBound, hqLower, hratioGrowth, hgrowth]
    exact_mod_cast hKreal
  have hmaxJumps : ⌊(threshold + Delta) / binWidth⌋₊ + 1 ≤ q := by
    simpa [K] using hKleq
  have hsqrt : Real.sqrt t = Delta ^ (eta / 2) := by
    dsimp [t]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hDeltaPos.le]
    congr 1
    ring
  have hentropy : Real.log 2 / Real.sqrt t ≤ d * eta := by
    rw [hsqrt]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hDeltaPos (eta / 2))).2
    simpa [mul_comm] using
      (div_le_iff₀ (mul_pos hd hetaPos)).1 hentropyGrowth
  have hscaledJump : d * B * t * maxJumpFactor ≤ d * eta * Delta ^ horizonPower := by
    calc
      d * B * t * maxJumpFactor = (d * eta * t) *
          (B * maxJumpFactor / eta) := by
            dsimp [t]
            field_simp [ne_of_gt hetaPos]
      _ ≤ (d * eta * t) * Delta ^ (horizonPower - eta) :=
            mul_le_mul_of_nonneg_left hconst (by positivity)
      _ = d * eta * Delta ^ horizonPower := by
            rw [hpowerDifference]
            dsimp [t]
            ring
  have hjump : d * (1 + 2 * eta) * t * ((K : ℝ) + 1) ≤ d * eta * z := by
    calc
      d * (1 + 2 * eta) * t * ((K : ℝ) + 1) ≤
          d * B * t * maxJumpFactor := by
            exact mul_le_mul_of_nonneg_left hjumpCountBound (by positivity)
      _ ≤ d * eta * Delta ^ horizonPower := hscaledJump
      _ ≤ d * eta * z := mul_le_mul_of_nonneg_left hzLower (by positivity)
  have hsum := measureReal_noLargeDropEvent_le_sum_jumpPatternProducts_of_uniformBlockBound
    ν horizon blockLength hpatternBound
    Delta threshold binWidth hbinWidthPos hwidthThreshold
  have hp : Real.exp ((binWidth + Delta) ^ (eta / 2) -
      blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hpositive : 0 < d * (1 + 2 * eta) * t := by positivity
    have hnonpos : -d * (1 + 2 * eta) * t ≤ 0 := by linarith
    exact honeBlock'.trans hnonpos
  have hfiniteBound := measureReal_noLargeDropEvent_le_jumpPatternCount_mul_pow_of_sumBound
    ν horizon blockLength Delta threshold binWidth hsum hp
  have hsmallBlock :
      Real.exp ((binWidth + Delta) ^ (eta / 2) -
        blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ≤
      Real.exp (-d * (1 + 2 * eta) * t) := by
    apply Real.exp_le_exp.mpr
    exact honeBlock'
  have hpow :
      Real.exp ((binWidth + Delta) ^ (eta / 2) -
        blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ^ (q - K) ≤
      Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hsmallBlock _
  have hfiniteBound' :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta threshold) ≤
        (2 : ℝ) ^ q * Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) := by
    calc
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta threshold) ≤
          (2 : ℝ) ^ q *
            Real.exp ((binWidth + Delta) ^ (eta / 2) -
              blockRate * ((blockLength : ℝ) / (binWidth + Delta) ^ 2)) ^ (q - K) := by
                simpa [q, K, binWidth, threshold, blockLength] using hfiniteBound
      _ ≤ (2 : ℝ) ^ q *
          Real.exp (-d * (1 + 2 * eta) * t) ^ (q - K) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfinal := jumpPatternProbability_le_exp (by positivity) (by positivity)
    hetaPos hd hqLower hqUpper hKleq hentropy hjump
  have hprobability :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta threshold) ≤
        Real.exp (-d * z) := hfiniteBound'.trans hfinal
  simpa [threshold, z] using hprobability

/-- Finite-variance no-large-drawdown estimate stated as Lemma 3.3 of Wang
Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, extending Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, Lemma 2.3 (2025,
arXiv:2512.23266). The block proof follows Wang Yiyang's Lemma 3.3:
discretize the running maximum, encode its jump blocks, and apply the uniform
block estimate of Chapter 3, Lemma 3.2. The one-block rate follows Aïdékon
and Hu, Lemma 4.1, together with Mogul'skii, *Small deviations in a space of
trajectories*, Theorem 3, Section 4, p. 764.

For
\[
  B_{L,\Delta,c}:=\left\{Y_L\leq\frac{\Delta}{c},\quad
    \min_{0\leq i\leq j\leq L}(Y_j-Y_i)\geq-\Delta\right\},
\]
the conclusion is `P(B_{L,Δ,c}) ≤ exp(-d L / Δ²)` whenever `Δ` is large
enough and `L ≥ Δ^(2+c)`. -/
theorem measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance c d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance) (hc : 0 < c) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ horizon : ℕ,
        Delta ^ (2 + c) ≤ (horizon : ℝ) →
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / c)) ≤
          Real.exp (-d * ((horizon : ℝ) / Delta ^ 2)) := by
  by_cases hcSmall : c < 1 / 2
  · obtain ⟨Delta₀, hDelta₀, hbound⟩ :=
      exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers
        ν hν hsquare hvariance hc hc hd hcritical
    refine ⟨Delta₀, hDelta₀, ?_⟩
    intro Delta hDelta horizon hhorizon
    exact hbound Delta hDelta horizon hhorizon
  · let c' : ℝ := 1 / 2 - 1 / (2 + c)
    have hcHalf : 1 / 2 ≤ c := le_of_not_gt hcSmall
    have hcPlus : 0 < 2 + c := by linarith
    have hc'Form : c' = c / (2 * (2 + c)) := by
      dsimp [c']
      field_simp [ne_of_gt hcPlus]
      ring
    have hc'Pos : 0 < c' := by
      rw [hc'Form]
      positivity
    have hc'LtHalf : c' < 1 / 2 := by
      dsimp [c']
      have hreciprocal : 0 < 1 / (2 + c) := by positivity
      linarith
    have hc'LeC : c' ≤ c := le_trans hc'LtHalf.le hcHalf
    have htransformedExponent : 2 / (1 - 2 * c') = 2 + c := by
      have hdenominator : 1 - 2 * c' = 2 / (2 + c) := by
        dsimp [c']
        field_simp [ne_of_gt hcPlus]
        ring
      rw [hdenominator]
      field_simp [ne_of_gt hcPlus]
    have hhorizonPowerPos : 0 < 2 / (1 - 2 * c') - 2 := by
      rw [htransformedExponent]
      linarith
    obtain ⟨Delta₀, hDelta₀, hbound⟩ :=
      exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers
        (endpointPower := c') (horizonPower := 2 / (1 - 2 * c') - 2)
        ν hν hsquare hvariance hc'Pos hhorizonPowerPos hd hcritical
    refine ⟨Delta₀, hDelta₀, ?_⟩
    intro Delta hDelta horizon hhorizon
    have hhorizon' :
        Delta ^ (2 + (2 / (1 - 2 * c') - 2)) ≤ (horizon : ℝ) := by
      have hexponent : 2 + (2 / (1 - 2 * c') - 2) = 2 + c := by
        rw [htransformedExponent]
        ring
      rw [hexponent]
      exact hhorizon
    have htransformedBound := hbound Delta hDelta horizon hhorizon'
    have hthreshold : Delta / c ≤ Delta / c' := by
      apply (div_le_div_iff₀ hc hc'Pos).2
      exact mul_le_mul_of_nonneg_left hc'LeC (by linarith : 0 ≤ Delta)
    have heventSubset :
        noLargeDropEndpointBelowEvent horizon Delta (Delta / c) ⊆
          noLargeDropEndpointBelowEvent horizon Delta (Delta / c') := by
      intro increment hevent
      exact ⟨hevent.1, le_trans hevent.2 hthreshold⟩
    calc
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / c)) ≤
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / c')) :=
        measureReal_mono heventSubset
          (measure_ne_top (iidSequenceLaw ν) _)
      _ ≤ Real.exp (-d * ((horizon : ℝ) / Delta ^ 2)) := by
        simpa using htransformedBound

/-- The finite-variance endpoint estimate is uniform over all horizons that
dominate a prescribed power of the width. This is a direct scaling of the
finite-variance form of Wang Yiyang, Chapter 3, Lemma 3.3: choose the smaller
of the requested horizon exponent and the endpoint exponent, then apply the
drawdown estimate above. -/
theorem exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (endpointRatio target p : ℝ)
    (hEndpointRatio : 0 < endpointRatio)
    (htarget : 0 < target)
    (htargetCritical : target < Real.pi ^ 2 / 2)
    (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, delta0 ≤ delta → ∀ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) →
          iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (delta / endpointRatio)) ≤
            ENNReal.ofReal (Real.exp
              (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2)) := by
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_integral_ne_zero (by
      rw [hν.2]
      exact ne_of_gt (sq_pos_of_pos hsigma))
  have hvariance : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have htargetRate : 0 < target * sigma ^ 2 := mul_pos htarget hvariance
  have hcritical : target * sigma ^ 2 < (Real.pi ^ 2 / 2) * sigma ^ 2 :=
    mul_lt_mul_of_pos_right htargetCritical hvariance
  let endpointPower : ℝ := min p endpointRatio
  have hendpointPowerPos : 0 < endpointPower := by
    dsimp [endpointPower]
    exact lt_min hp hEndpointRatio
  have hendpointPowerLeP : endpointPower ≤ p := min_le_left _ _
  have hendpointPowerLeRatio : endpointPower ≤ endpointRatio :=
    min_le_right _ _
  obtain ⟨Delta0, hDelta0, hbound⟩ :=
    measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance
      ν hν hsquare hvariance hendpointPowerPos htargetRate hcritical
  refine ⟨Delta0, lt_of_lt_of_le (by norm_num) hDelta0, ?_⟩
  intro delta hdelta horizon hlarge
  have hdeltaOne : 1 ≤ delta := hDelta0.trans hdelta
  have hdeltaPos : 0 < delta := lt_of_lt_of_le (by norm_num) hdeltaOne
  have hpower : delta ^ (2 + endpointPower) ≤ delta ^ (2 + p) :=
    Real.rpow_le_rpow_of_exponent_le hdeltaOne (by linarith)
  have hlarge' : delta ^ (2 + endpointPower) ≤ (horizon : ℝ) :=
    hpower.trans hlarge
  have hbound' := hbound delta hdelta horizon hlarge'
  have hthreshold : delta / endpointRatio ≤ delta / endpointPower :=
    (div_le_div_iff₀ hEndpointRatio hendpointPowerPos).2
      (mul_le_mul_of_nonneg_left hendpointPowerLeRatio hdeltaPos.le)
  have hsubset :
      noLargeDropEndpointBelowEvent horizon delta
          (delta / endpointRatio) ⊆
        noLargeDropEndpointBelowEvent horizon delta
          (delta / endpointPower) := by
    intro increment hevent
    exact ⟨hevent.1, hevent.2.trans hthreshold⟩
  have hrealBound :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta
            (delta / endpointRatio)) ≤
        Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2) := by
    calc
      _ ≤ (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta
            (delta / endpointPower)) :=
        measureReal_mono hsubset (measure_ne_top (iidSequenceLaw ν) _)
      _ ≤ Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2) := by
        have hexponent : -(target * sigma ^ 2) *
            ((horizon : ℝ) / delta ^ 2) =
            -target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2 := by ring
        rw [← hexponent]
        exact hbound'
  let event := noLargeDropEndpointBelowEvent horizon delta
    (delta / endpointRatio)
  let q : ℝ≥0∞ := iidSequenceLaw ν event
  have hqle : q ≤ 1 := by
    calc
      q ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hqtop : q ≠ ∞ := ne_of_lt (lt_of_le_of_lt hqle ENNReal.one_lt_top)
  have hrealQ : q.toReal ≤
      Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2) := by
    simpa [q, event, Measure.real] using hrealBound
  change q ≤ ENNReal.ofReal
    (Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2))
  rw [← ENNReal.ofReal_toReal hqtop]
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).2 hrealQ

/-- The quotient by a floor-rounded diffusive block length diverges whenever
the horizon is large compared with the square of the spatial scale. The
statement is phrased for a real scale, so the deterministic result can be
used with any positive diffusive block constant. -/
theorem tendsto_diffusiveBlockCount_atTop_of_horizonRatio
    {horizon : ℕ → ℕ} {delta : ℕ → ℝ} {A : ℝ}
    (hdelta : Tendsto delta atTop atTop) (hA : 0 < A)
    (hratio : Tendsto (fun n => (horizon n : ℝ) / delta n ^ 2)
      atTop atTop) :
    Tendsto (fun n => horizon n / ⌊A * delta n ^ 2⌋₊) atTop atTop := by
  let length : ℕ → ℕ := fun n => ⌊A * delta n ^ 2⌋₊
  let blocks : ℕ → ℕ := fun n => horizon n / length n
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n :=
    hdelta.eventually_gt_atTop 0
  have hlengthTop : Tendsto length atTop atTop := by
    apply Asymptotics.tendsto_floorBlockLength_atTop
    have hsquare : Tendsto (fun n => delta n * delta n) atTop atTop :=
      hdelta.atTop_mul_atTop₀ hdelta
    simpa [length, Asymptotics.floorBlockLength, pow_two, mul_comm] using
      hsquare.const_mul_atTop hA
  have hlengthPos : ∀ᶠ n : ℕ in atTop, 0 < length n :=
    hlengthTop.eventually_gt_atTop 0
  have hlengthLe : ∀ᶠ n : ℕ in atTop,
      (length n : ℝ) ≤ A * delta n ^ 2 := by
    filter_upwards [hdeltaPos] with n hδ
    exact Nat.floor_le (mul_nonneg hA.le (sq_nonneg (delta n)))
  have hratioLower : ∀ᶠ n : ℕ in atTop,
      (horizon n : ℝ) / (length n : ℝ) ≥
        ((horizon n : ℝ) / delta n ^ 2) / A := by
    filter_upwards [hdeltaPos, hlengthPos, hlengthLe] with n hδ hm hle
    have hδsq : 0 < delta n ^ 2 := sq_pos_of_pos hδ
    have hlenReal : 0 < (length n : ℝ) := by exact_mod_cast hm
    have hAδ : 0 < A * delta n ^ 2 := mul_pos hA hδsq
    calc
      ((horizon n : ℝ) / delta n ^ 2) / A =
          (horizon n : ℝ) / (A * delta n ^ 2) := by
            field_simp [hA.ne', hδsq.ne']
      _ ≤ (horizon n : ℝ) / (length n : ℝ) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlenReal hle
  have hratioLowerTop : Tendsto
      (fun n => ((horizon n : ℝ) / delta n ^ 2) / A) atTop atTop :=
    by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm] using
        hratio.const_mul_atTop (inv_pos.mpr hA)
  have hratioBlocks : Tendsto (fun n =>
      (horizon n : ℝ) / (length n : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_mono' atTop hratioLower hratioLowerTop
  have hblocks : Tendsto blocks atTop atTop := by
    refine tendsto_atTop.2 fun k => ?_
    have hkraw : ∀ᶠ n : ℕ in atTop,
        ((k + 1 : ℕ) : ℝ) ≤ (horizon n : ℝ) / (length n : ℝ) :=
      hratioBlocks.eventually
        (eventually_ge_atTop ((k + 1 : ℕ) : ℝ))
    have hk : ∀ᶠ n : ℕ in atTop,
        ((k + 1 : ℕ) : ℝ) ≤ (horizon n : ℝ) / (length n : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hkraw
    filter_upwards [hk, hlengthPos] with n hk hm
    have hmul : ((k + 1 : ℕ) : ℝ) * (length n : ℝ) ≤ (horizon n : ℝ) :=
      (le_div_iff₀ (by exact_mod_cast hm)).1 hk
    have hmulNat : (k + 1) * length n ≤ horizon n := by exact_mod_cast hmul
    have hdiv : k + 1 ≤ horizon n / length n :=
      (Nat.le_div_iff_mul_le hm).2 (by simpa [Nat.succ_mul] using hmulNat)
    dsimp [blocks, length] at hdiv ⊢
    omega
  simpa [blocks, length] using hblocks

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
