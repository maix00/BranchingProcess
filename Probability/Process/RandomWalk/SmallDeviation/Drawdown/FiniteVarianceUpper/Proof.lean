/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.ConditionalBlocks
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Bounded-drawdown walk events

Public definitions and theorems (write `S_i` for the additive path
and `P` for its IID law):

- `drawdownBlockStart`, `drawdownBlockCount`, and `drawdownBlockRemainder`:
  the block starts $r+j\ell$, count $q=\lfloor L/\ell\rfloor$, and
  initial remainder $r=L\bmod\ell$.
- `drawdownDiscretizedMaximum`, `drawdownMaximumJumpSet`,
  `drawdownRunningMaximumBins`, and `drawdownRunningMaximumJumpSet`:
  the rounded running maximum, its spatial-bin indices, and the blocks
  at which that bin index increases.
- `drawdownJumpPatternTubeEvent`, `drawdownJumpPatternTubeIntersection`,
  `drawdownJumpPatternBound`, and `drawdownAdmissibleJumpPatterns`:
  the block event and product factor for a fixed jump set $J$, its
  intersection over all blocks, and the finite family $|J|\le K$.

- `drawdownBlockStart_last_eq_horizon`: the remainder plus `qℓ` equals `L`.
- `eventually_drawdownFloorBlockLength_bounds`: for $\eta>0$ and large
  $\Delta$, $\Delta^{2+\eta/2}\le\lfloor\Delta^{2+\eta}\rfloor
  \le\Delta^{2+\eta}$.
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

- `exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers`:
  the finite-variance drawdown bound for a small endpoint exponent and a
  superquadratic horizon exponent.


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
\(M_j-w-\Delta<S_i\leq M_j\).
The conditional one-block estimate is imported from `ConditionalBlocks` and
uses Wang Yiyang, Chapter 3, Lemma 3.2.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

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
theorem exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
