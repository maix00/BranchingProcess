/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Survival.Basic
public import Probability.Process.RandomWalk.Path.Block.Law.Basic
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival.Conditioning
public import Probability.Sequence.IID.StoppingTime

/-!
# Almost-sure existence of a first surviving window

The public theorem in this module is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_exists_firstSurvivingWindow_eq_one`:
  if $\nu((0,\infty))>0$, then an IID walk has a first surviving
  length-$n$ window with probability one.

This is the finite-$T_n$ step before Lemma 3.1 in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay
Positive*, p. 482, DOI 10.1214/aop/1176996098. Its recurrence argument
uses Vladislav Vysotsky, *Positivity of integrated random walks*,
Section 3.1, equation (17), DOI 10.1214/12-AIHP487.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The first length-$n$ surviving window exists almost surely. This
supplies the $T_n<\infty$ step preceding Lemma 3.1 in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay
Positive*, p. 482, DOI 10.1214/aop/1176996098. The recurrence input is
Vladislav Vysotsky, *Positivity of integrated random walks*, Section 3.1,
equation (17), DOI 10.1214/12-AIHP487. -/
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

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
