/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Adapted.Filtration
public import Probability.Process.RandomWalk.Path.Survival
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival.Conditioning
public import Probability.Sequence.IID.StoppingTime
public import Algebra.BigOperators.PartialSum

/-!
# Independent future blocks at first surviving windows

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.NoEarlierSurvivingPrefix`:
  $B_j^c$, where $B_j$ is Bolthausen's union of earlier starts whose
  paths remain above their starting levels through $\min(j,s+n)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.isFirstSurvivingWindow_iff_prefixFailure_and_survives`:
  $\{T_n=j\}=B_j^c\cap\{S_{j+k}\ge S_j,1\le k\le n\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measurableSet_noEarlierSurvivingPrefix_prefix`:
  $B_j^c$ is measurable from the first $j$ increments.

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_prefixFailure_inter_block_eq_mul`:
  for an IID increment law, a prefix event determined by
  the first $m$ increments is independent of any measurable event of the
  following length-$n$ increment block.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_inter_block_eq_mul`:
  the joint mass of a first surviving window at $m$ and a finite block
  event equals the prefix-event mass times the probability of that block
  event intersected with finite survival.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_block_union_eq_tsum`:
  $\mathbb P(\bigcup_m(F_{n,m}\cap\{B_m\in A\}))
  =(\sum_m\mathbb P(C_{n,m}))\mathbb P(B_0\in A\cap C_n)$,
  where $F_{n,m}$ is the first surviving window and $C_{n,m}$ its
  prefix-measurable event $B_m^c$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_exists_firstSurvivingWindow_eq_one`:
  if $\nu((0,\infty))>0$, then $\mathbb P(T_n<\infty)=1$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_block_union_eq_conditionalBlock`:
  for a measurable block event $A$,
  $\mathbb P(B_{T_n}\in A)=\mathbb P(B_0\in A\cap C_n)/\mathbb P(C_n)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_partialSums_bounded_eq_conditional`:
  for thresholds $a_1,\ldots,a_n$, the probability that all partial
  sums of the first surviving block satisfy $Z_k\le a_k$ equals the
  corresponding conditional probability for $S_1,\ldots,S_n$.

This follows the prefix event $B_j$ in Lemma 3.1 of Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480–485,
DOI 10.1214/aop/1176996098. The path-transform interpretation is also
given by Vladislav Vysotsky, *Positivity of integrated random walks*,
Ann. Inst. H. Poincaré Probab. Stat. 50(1) (2014), Section 3.1,
equation (17), DOI 10.1214/12-AIHP487.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The complement of Bolthausen's prefix event $B_j$: every earlier
start $s<j$ has already fallen strictly below $S_s$ by time
$\min(j,s+n)$. This depends only on the first $j$ increments.
See Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Lemma 3.1, p. 482,
DOI 10.1214/aop/1176996098. -/
def NoEarlierSurvivingPrefix (n start : ℕ) (increment : ℕ → ℝ) : Prop :=
  ¬ ∃ s : Fin start, ∀ r : ℕ,
    (s : ℕ) < r → r ≤ min start ((s : ℕ) + n) →
      AdditivePath.displacement s increment ≤
        AdditivePath.displacement r increment

/-- Bolthausen's first window at $j$ is the intersection of the
prefix event $B_j^c$ and survival of the independent length-$n$ suffix.
This is the set identity used in Lemma 3.1, pp. 482--483. -/
theorem isFirstSurvivingWindow_iff_prefixFailure_and_survives
    (n start : ℕ) (increment : ℕ → ℝ) :
    IsFirstSurvivingWindow n start increment ↔
      NoEarlierSurvivingPrefix n start increment ∧
        SurvivesNonnegative n (fun k => increment (start + k)) := by
  constructor
  · intro hfirst
    refine ⟨?_, hfirst.1⟩
    intro hprefix
    obtain ⟨s, hs⟩ := hprefix
    apply hfirst.2 s
    apply (SurvivesNonnegative.shift_iff n s increment).2
    intro k
    let r := (s : ℕ) + ((k : ℕ) + 1)
    have hrle : r ≤ (s : ℕ) + n := by
      dsimp [r]
      omega
    by_cases hr : r ≤ start
    · exact hs r (by dsimp [r]; omega) (le_min hr hrle)
    · have hbefore : AdditivePath.displacement s increment ≤
          AdditivePath.displacement start increment :=
        hs start s.isLt (le_min le_rfl (by omega))
      have hindex : r - start - 1 < n := by
        dsimp [r] at *
        omega
      have hafter :=
        (SurvivesNonnegative.shift_iff n start increment).1 hfirst.1
          ⟨r - start - 1, hindex⟩
      have hrpos : start + ((r - start - 1) + 1) = r := by omega
      rw [hrpos] at hafter
      exact hbefore.trans hafter
  · rintro ⟨hprefix, hsurvive⟩
    refine ⟨hsurvive, ?_⟩
    intro s hwindow
    apply hprefix
    refine ⟨s, ?_⟩
    intro r hsr hrbound
    have hrle : r ≤ (s : ℕ) + n := (le_min_iff.mp hrbound).2
    have hindex : r - (s : ℕ) - 1 < n := by omega
    have hposition :=
      (SurvivesNonnegative.shift_iff n s increment).1 hwindow
        ⟨r - (s : ℕ) - 1, hindex⟩
    have hrpos : (s : ℕ) + ((r - (s : ℕ) - 1) + 1) = r := by omega
    rwa [hrpos] at hposition

/-- The event $B_j^c$ in Bolthausen's Lemma 3.1 is measurable with
respect to the first $j$ increments. -/
theorem measurableSet_noEarlierSurvivingPrefix_prefix (n start : ℕ) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) start]
      {increment : ℕ → ℝ | NoEarlierSurvivingPrefix n start increment} := by
  let viable (s : Fin start) : Set (ℕ → ℝ) :=
    ⋂ r : ℕ,
      {increment | (s : ℕ) < r → r ≤ min start ((s : ℕ) + n) →
        AdditivePath.displacement s increment ≤
          AdditivePath.displacement r increment}
  have hviable (s : Fin start) :
      MeasurableSet[sequencePrefixFiltration (E := ℝ) start] (viable s) := by
    apply MeasurableSet.iInter
    intro r
    by_cases hr : (s : ℕ) < r ∧ r ≤ min start ((s : ℕ) + n)
    · have hrstart : r ≤ start := (le_min_iff.mp hr.2).1
      have hset :
          {increment : ℕ → ℝ | (s : ℕ) < r →
            r ≤ min start ((s : ℕ) + n) →
            AdditivePath.displacement s increment ≤
              AdditivePath.displacement r increment} =
          {increment | AdditivePath.displacement s increment ≤
            AdditivePath.displacement r increment} := by
        ext increment
        simp [hr.1, hr.2]
      rw [hset]
      exact measurableSet_le
        (displacement_measurable_prefix (E := ℝ) s.isLt.le)
        (displacement_measurable_prefix (E := ℝ) hrstart)
    · have hset :
          {increment : ℕ → ℝ | (s : ℕ) < r →
            r ≤ min start ((s : ℕ) + n) →
            AdditivePath.displacement s increment ≤
              AdditivePath.displacement r increment} = Set.univ := by
        ext increment
        by_cases hsr : (s : ℕ) < r
        · have hrle : ¬ r ≤ min start ((s : ℕ) + n) := by
            intro hle
            exact hr ⟨hsr, hle⟩
          simp [hsr, hrle]
        · simp [hsr]
      rw [hset]
      exact MeasurableSet.univ
  rw [show {increment : ℕ → ℝ | NoEarlierSurvivingPrefix n start increment} =
    (⋃ s : Fin start, viable s)ᶜ by
      ext increment
      simp [NoEarlierSurvivingPrefix, viable]]
  exact (MeasurableSet.iUnion hviable).compl


/-- A prefixFailure first-window start depends only on the past and therefore
factors from every event of the following IID increment block. -/
theorem measure_prefixFailure_inter_block_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n start : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
      ({increment | NoEarlierSurvivingPrefix n start increment} ∩
        (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) =
      (iidSequenceLaw ν)
        {increment | NoEarlierSurvivingPrefix n start increment} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' event) := by
  let past := Combinatorics.Sequence.blockCoordinates (E := ℝ) 0 start
  let future := Combinatorics.Sequence.blockCoordinates (E := ℝ) start n
  have hpast : MeasurableSet[MeasurableSpace.comap past inferInstance]
      {increment : ℕ → ℝ | NoEarlierSurvivingPrefix n start increment} := by
    rw [show MeasurableSpace.comap past inferInstance =
      sequencePrefixFiltration (E := ℝ) start by
        exact (sequencePrefixFiltration_eq_comap_blockCoordinates start).symm]
    exact measurableSet_noEarlierSurvivingPrefix_prefix n start
  obtain ⟨pastEvent, hpastEvent, hpastPreimage⟩ :=
    (MeasurableSpace.measurableSet_comap).1 hpast
  have hindep := indepFun_blockCoordinates_blockCoordinates ν 0 start n
  have hfactor := hindep.measure_inter_preimage_eq_mul
    pastEvent event hpastEvent hevent
  have hfuture :
      (iidSequenceLaw ν) (future ⁻¹' event) =
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' event) := by
    calc
      _ = ((iidSequenceLaw ν).map future) event :=
        (Measure.map_apply (μ := iidSequenceLaw ν)
          (measurable_blockCoordinates start n) hevent).symm
      _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 n)) event := by
        rw [iidSequenceLaw_map_blockCoordinates]
      _ = _ := Measure.map_apply (μ := iidSequenceLaw ν)
        (measurable_blockCoordinates 0 n) hevent
  simpa only [past, future, Nat.zero_add, ← hpastPreimage, hfuture]
    using hfactor

/-- At a fixed starting time, the first surviving-window event factors
into its prefix prefixFailure event and the finite surviving future block. -/
theorem measure_firstWindow_inter_block_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n start : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
      ({increment | IsFirstSurvivingWindow n start increment} ∩
        (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) =
      (iidSequenceLaw ν)
        {increment | NoEarlierSurvivingPrefix n start increment} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
            (event ∩ {block | FiniteSurvivesNonnegative block})) := by
  have hset :
      {increment : ℕ → ℝ |
        IsFirstSurvivingWindow n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event =
        {increment | NoEarlierSurvivingPrefix n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹'
            (event ∩ {block | FiniteSurvivesNonnegative block}) := by
    ext increment
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [isFirstSurvivingWindow_iff_prefixFailure_and_survives,
      ← finiteSurvivesNonnegative_blockCoordinates_iff]
    tauto
  rw [hset]
  exact measure_prefixFailure_inter_block_eq_mul ν n start _
    (hevent.inter (measurableSet_finiteSurvivesNonnegative n))

/-- Countable additivity of the disjoint first-window events turns the
fixed-start factorization into a path-law identity. Almost-sure existence
of a first window is a separate recurrence step in the argument described by
Vladislav Vysotsky, *Positivity of integrated random walks*, Section 3.1,
equation (17), DOI 10.1214/12-AIHP487. -/
theorem measure_firstWindow_block_union_eq_tsum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
      (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) =
      (∑' start : ℕ,
        (iidSequenceLaw ν)
          {increment | NoEarlierSurvivingPrefix n start increment}) *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
            (event ∩ {block | FiniteSurvivesNonnegative block})) := by
  let μ := iidSequenceLaw ν
  let first : ℕ → Set (ℕ → ℝ) := fun start =>
    {increment | IsFirstSurvivingWindow n start increment}
  let block : ℕ → Set (ℕ → ℝ) := fun start =>
    (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event
  let prefixFailure : ℕ → Set (ℕ → ℝ) := fun start =>
    {increment | NoEarlierSurvivingPrefix n start increment}
  let p : ℝ≥0∞ := μ
    ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
      (event ∩ {block | FiniteSurvivesNonnegative block}))
  have hpair : Pairwise (fun i j => Disjoint (first i) (first j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro increment hi hj
    exact hij (hi.unique hj)
  have hpairBlock : Pairwise
      (fun i j => Disjoint (first i ∩ block i) (first j ∩ block j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro increment hi hj
    exact (Set.disjoint_left.mp (hpair hij)) hi.1 hj.1
  have hfirstMeasurable (start : ℕ) : MeasurableSet (first start) :=
    measurableSet_isFirstSurvivingWindow n start
  have hpairMeasurable (start : ℕ) :
      MeasurableSet (first start ∩ block start) :=
    (hfirstMeasurable start).inter
      (hevent.preimage (measurable_blockCoordinates start n))
  have hpairMass (start : ℕ) :
      μ (first start ∩ block start) = μ (prefixFailure start) * p := by
    exact measure_firstWindow_inter_block_eq_mul ν n start event hevent
  calc
    μ (⋃ start, first start ∩ block start) =
        ∑' start, μ (first start ∩ block start) :=
      measure_iUnion hpairBlock hpairMeasurable
    _ = ∑' start, μ (prefixFailure start) * p :=
      tsum_congr hpairMass
    _ = (∑' start, μ (prefixFailure start)) * p :=
      ENNReal.tsum_mul_right

/-- The first length-$n$ surviving window exists almost surely. This
supplies the $T_n<\infty$ step preceding Lemma 3.1 in Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to stay
positive*, p. 482, DOI 10.1214/aop/1176996098. -/
theorem measure_exists_firstSurvivingWindow_eq_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0)) (n : ℕ) :
    (iidSequenceLaw ν)
      (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment}) = 1 := by
  let μ := iidSequenceLaw ν
  let good : Set (Fin n → ℝ) :=
    {block | FiniteSurvivesNonnegative block}
  let bad : Set (ℕ → ℝ) :=
    {increment | ∀ start : ℕ,
      ¬ SurvivesNonnegative n (fun j => increment (start + j))}
  let q : ℝ≥0∞ := μ
    ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' goodᶜ)
  have hgoodMeas : MeasurableSet good :=
    measurableSet_finiteSurvivesNonnegative n
  have hbadMeas : MeasurableSet bad := by
    rw [show bad =
      ⋂ start : ℕ,
        {increment : ℕ → ℝ | SurvivesNonnegative n
          (fun j => increment (start + j))}ᶜ by
      ext increment
      simp [bad]]
    exact MeasurableSet.iInter fun start =>
      ((measurableSet_survivesNonnegative n).preimage
        (measurable_natAdd start)).compl
  have hqeq : q = 1 - μ
      ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' good) := by
    dsimp [q]
    rw [measure_compl
      (hgoodMeas.preimage (measurable_blockCoordinates 0 n))
      (by finiteness)]
    simp
  have hgoodProb : μ
      ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' good) =
      μ {increment | SurvivesNonnegative n increment} := by
    congr 1
    ext increment
    change FiniteSurvivesNonnegative
      (Combinatorics.Sequence.blockCoordinates 0 n increment) ↔
        SurvivesNonnegative n increment
    simpa only [zero_add] using
      (finiteSurvivesNonnegative_blockCoordinates_iff n 0 increment)
  have hq : q < 1 := by
    rw [hqeq, hgoodProb]
    apply ENNReal.sub_lt_self ENNReal.one_ne_top (by norm_num)
    exact (survivalProbability_pos_of_positiveIncrement ν hpositive n).ne'
  have hbadSubset (k : ℕ) : bad ⊆
      {increment : ℕ → ℝ | ∀ j : Fin k,
        Combinatorics.Sequence.blockCoordinates (j * n) n increment ∈ goodᶜ} := by
    intro increment hbad j
    change ¬ FiniteSurvivesNonnegative
      (Combinatorics.Sequence.blockCoordinates (j * n) n increment)
    exact mt (finiteSurvivesNonnegative_blockCoordinates_iff n (j * n) increment).1
      (hbad (j * n))
  have hbound (k : ℕ) : μ bad ≤ q ^ k := by
    calc
      μ bad ≤ μ {increment : ℕ → ℝ | ∀ j : Fin k,
          Combinatorics.Sequence.blockCoordinates (j * n) n increment ∈ goodᶜ} :=
        measure_mono (hbadSubset k)
      _ = q ^ k := by
        exact iidSequenceLaw_measure_forall_consecutiveBlockEvent
          ν k n goodᶜ hgoodMeas.compl
  have hzero : μ bad = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hbound
    · exact bot_le
  have hcover : (⋃ start : ℕ,
      {increment | IsFirstSurvivingWindow n start increment}) = badᶜ := by
    ext increment
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff,
      bad, not_forall, not_not]
    constructor
    · rintro ⟨start, hfirst⟩
      exact ⟨start, hfirst.1⟩
    · rintro ⟨start, hsurvive⟩
      obtain ⟨first, _, hfirst⟩ :=
        exists_firstSurvivingWindow_le hsurvive
      exact ⟨first, hfirst⟩
  rw [hcover, measure_compl hbadMeas (by finiteness), hzero]
  simp

/-- The law of the first surviving length-$n$ increment block is the
law of the initial block conditioned to survive. This is the measurable
finite-block form of Lemma 3.1 in Erwin Bolthausen, *On a functional
central limit theorem for random walks conditioned to stay positive*,
pp. 482--483, DOI 10.1214/aop/1176996098. -/
theorem measure_firstWindow_block_union_eq_conditionalBlock
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (n : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
      (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) =
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          (event ∩ {block | FiniteSurvivesNonnegative block})) /
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block}) := by
  let μ := iidSequenceLaw ν
  let s : ℝ≥0∞ := ∑' start : ℕ,
    μ {increment | NoEarlierSurvivingPrefix n start increment}
  let q : ℝ≥0∞ := μ
    ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
      {block | FiniteSurvivesNonnegative block})
  let p : ℝ≥0∞ := μ
    ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
      (event ∩ {block | FiniteSurvivesNonnegative block}))
  have hqpos : 0 < q := by
    have hp := survivalProbability_pos_of_positiveIncrement ν hpositive n
    have hset :
        (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block} =
        {increment | SurvivesNonnegative n increment} := by
      ext increment
      change FiniteSurvivesNonnegative
        (Combinatorics.Sequence.blockCoordinates 0 n increment) ↔
          SurvivesNonnegative n increment
      simpa only [zero_add] using
        (finiteSurvivesNonnegative_blockCoordinates_iff n 0 increment)
    simpa only [q, hset] using hp
  have hqfinite : q ≠ ∞ := measure_ne_top _ _
  have hnormal : s * q = 1 := by
    have h := measure_firstWindow_block_union_eq_tsum ν n Set.univ
      MeasurableSet.univ
    have hcover := measure_exists_firstSurvivingWindow_eq_one ν hpositive n
    have h' : μ (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment}) =
        s * q := by
      simpa only [Set.preimage_univ, Set.inter_univ, Set.univ_inter,
        s, q] using h
    rw [hcover] at h'
    exact h'.symm
  have hmain := measure_firstWindow_block_union_eq_tsum ν n event hevent
  apply (ENNReal.eq_div_iff hqpos.ne' hqfinite).2
  rw [hmain]
  change q * (s * p) = p
  calc
    q * (s * p) = (s * q) * p := by ac_rfl
    _ = p := by rw [hnormal]; simp

/-- Bolthausen's Lemma 3.1 in its displayed finite-dimensional form:
the partial sums of the first surviving length-`n` block have the law
of the original partial sums conditioned on nonnegative survival.
See Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Lemma 3.1, p. 482,
DOI 10.1214/aop/1176996098. -/
theorem measure_firstWindow_partialSums_bounded_eq_conditional
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (n : ℕ) (threshold : Fin n → ℝ) :
    (iidSequenceLaw ν)
      (⋃ start : ℕ,
        {increment | IsFirstSurvivingWindow n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹'
            {block : Fin n → ℝ |
              ∀ k : Fin n, Fin.partialSum block k.succ ≤ threshold k}) =
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          ({block : Fin n → ℝ |
            ∀ k : Fin n, Fin.partialSum block k.succ ≤ threshold k} ∩
            {block | FiniteSurvivesNonnegative block})) /
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block}) := by
  apply measure_firstWindow_block_union_eq_conditionalBlock ν hpositive n
  rw [show {block : Fin n → ℝ |
      ∀ k : Fin n, Fin.partialSum block k.succ ≤ threshold k} =
      ⋂ k : Fin n,
        {block | Fin.partialSum block k.succ ≤ threshold k} by
      ext block
      simp]
  apply MeasurableSet.iInter
  intro k
  have hsum (time : Fin (n + 1)) :
      Measurable (fun block : Fin n → ℝ => Fin.partialSum block time) := by
    induction time using Fin.induction with
    | zero => exact measurable_const
    | succ time ih =>
      have heq : (fun block : Fin n → ℝ => Fin.partialSum block time.succ) =
          (fun block => Fin.partialSum block time.castSucc) +
            (fun block => block time) := by
        funext block
        simp only [Fin.partialSum_succ, Pi.add_apply]
      exact heq ▸ ih.add (measurable_pi_apply time)
  exact measurableSet_le
    (hsum k.succ) measurable_const


end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
