/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Definition
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival.Conditioning
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Sequence.IID.Basic
import Probability.Sequence.IID.Blocks.StoppingTime
import Probability.Sequence.IID.Blocks.Consecutive

/-!
# First-window block factorization lemmas

The declaration in this module is a proof-specific lemma for the
finite-dimensional first-window law:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_block_union_eq_tsum`
  sums the disjoint fixed-start
  probabilities over all possible starts.

They formalize the block-decomposition steps in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay
Positive*, Lemma 3.1, pp. 482--483, DOI 10.1214/aop/1176996098. The
countable-additivity step uses the almost-sure first-window existence
argument related to Vladislav Vysotsky, *Positivity of integrated random
walks*, Section 3.1, equation (17), DOI 10.1214/12-AIHP487.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- A prefix-failure first-window start depends only on the past and therefore
factors from every event of the following IID increment block. This is the
independent-block factorization in Erwin Bolthausen, *On a Functional Central
Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 3.1,
pp. 482--483, DOI 10.1214/aop/1176996098. -/
private lemma measure_prefixFailure_inter_block_eq_mul
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
into its prefix-failure event and the finite surviving future block. This is
the fixed-start factorization in Erwin Bolthausen, *On a Functional Central
Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 3.1,
pp. 482--483, DOI 10.1214/aop/1176996098. -/
private lemma measure_firstWindow_inter_block_eq_mul
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
fixed-start factorization into the path-law identity used in Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks
Conditioned to Stay Positive*, Lemma 3.1, pp. 482--483,
DOI 10.1214/aop/1176996098. Almost-sure existence of the first window uses
Vladislav Vysotsky, *Positivity of integrated random walks*, Section 3.1,
equation (17), DOI 10.1214/12-AIHP487. -/
lemma measure_firstWindow_block_union_eq_tsum
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

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
