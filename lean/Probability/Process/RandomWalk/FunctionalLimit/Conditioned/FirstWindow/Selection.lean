/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Definition
public import Probability.Process.RandomWalk.Path.Interpolation.FiniteBlock
public import Probability.Process.RandomWalk.Path.Interpolation.FirstWindow
public import Probability.Process.Path.AboveStart.FirstWindow.Centered

/-!
# Selecting the first surviving random-walk block

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.firstSurvivingWindowIndex`:
  the least $j$ for which $S_{j+k}\ge S_j$ for $1\le k\le n$,
  with default value $0$ if no such $j$ exists.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.firstSurvivingWindowIndex_spec`:
  whenever such a window exists, the selected index satisfies
  `IsFirstSurvivingWindow`.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measurable_firstSurvivingWindowIndex`:
  the selected index is a measurable function of all increments.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.firstNonnegativeWindowStart_eq_firstSurvivingWindowIndex`:
  the first eligible start of the polygonal walk is exactly the selected
  lattice index divided by $n$ whenever a surviving window exists.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.selectedFirstSurvivingBlock`:
  the length-$n$ increment block starting at the selected index.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measurable_selectedFirstSurvivingBlock`:
  this finite block is measurable.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_selectedFirstSurvivingBlock_eq_conditionalBlock`:
  the selected block has the law of the initial block conditioned on
  survival, for every measurable finite-block event.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_map_selectedFirstSurvivingBlock_eq`:
  equality of the full finite-block probability measures.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_map_selectedFirstSurvivingBlockPath_eq`:
  the selected block's polygonal path has the same law as the initial
  polygonal path conditioned on survival.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_map_rebasedAtFirstSurvivingWindow_eq`:
  the whole-time walk rebased at its first discrete surviving window
  has the survival-conditioned unit-time path law.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_map_centeredFirstWindowShift_eq`:
  the centered continuous first-window map has the same
  survival-conditioned unit-time path law.

This is the random index $T_n$ and centered block $Z$ in
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 3.1 and Theorem 3.2,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The first index whose next `n` increments keep the walk above its
starting level; the value is zero on paths without such a window. -/
noncomputable def firstSurvivingWindowIndex (n : ℕ)
    (increment : ℕ → ℝ) : ℕ := by
  classical
  exact if h : ∃ start : ℕ,
      SurvivesNonnegative n (fun k => increment (start + k)) then
    Nat.find h
  else 0

/-- Whenever a surviving window exists, the selected index is its
first occurrence. -/
theorem firstSurvivingWindowIndex_spec
    (n : ℕ) (increment : ℕ → ℝ)
    (hex : ∃ start : ℕ,
      SurvivesNonnegative n (fun k => increment (start + k))) :
    IsFirstSurvivingWindow n
      (firstSurvivingWindowIndex n increment) increment := by
  classical
  rw [firstSurvivingWindowIndex, dite_eq_left hex]
  exact ⟨Nat.find_spec hex, fun j => Nat.find_min hex j.isLt⟩

/-- The continuous first-window time of the polygonal walk agrees
exactly with its first surviving lattice-window index. -/
theorem firstNonnegativeWindowStart_eq_firstSurvivingWindowIndex
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) (increment : ℕ → ℝ)
    (hex : ∃ start : ℕ,
      SurvivesNonnegative n (fun k => increment (start + k))) :
    firstNonnegativeWindowStart
        (normalizedLinearContinuousPathUnbounded scale n increment) =
      WithTop.some
        ((firstSurvivingWindowIndex n increment : ℝ≥0) / n) := by
  let j := firstSurvivingWindowIndex n increment
  let grid : ℝ≥0 := (j : ℝ≥0) / n
  have hfirst := firstSurvivingWindowIndex_spec n increment hex
  apply (firstNonnegativeWindowStart_eq_coe_iff _ grid).2
  constructor
  · exact (isNonnegativeWindowStart_grid_iff_survivesNonnegative
      scale hn hscale j increment).2 hfirst.1
  · intro s hs
    let k : ℕ := ⌊(n : ℝ) * (s : ℝ)⌋₊
    have hnonneg : 0 ≤ (n : ℝ) * (s : ℝ) :=
      mul_nonneg (Nat.cast_nonneg n) (NNReal.coe_nonneg s)
    have hklo : (k : ℝ) ≤ (n : ℝ) * (s : ℝ) :=
      Nat.floor_le hnonneg
    have hkhi : (n : ℝ) * (s : ℝ) < (k : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hkeligible := isNonnegativeWindowStart_grid_of_between
      scale hn hscale k increment s hklo hkhi hs
    have hksurv := (isNonnegativeWindowStart_grid_iff_survivesNonnegative
      scale hn hscale k increment).1 hkeligible
    have hjk : j ≤ k := by
      by_contra hnot
      exact (hfirst.2 ⟨k, Nat.lt_of_not_ge hnot⟩) hksurv
    have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    apply NNReal.coe_le_coe.mp
    change (j : ℝ) / n ≤ (s : ℝ)
    exact (div_le_iff₀ hnreal).2 (by
      calc
        (j : ℝ) ≤ k := by exact_mod_cast hjk
        _ ≤ (n : ℝ) * (s : ℝ) := hklo
        _ = (s : ℝ) * n := mul_comm _ _)

/-- An index satisfying the first-window predicate equals the selected
index. -/
private theorem firstSurvivingWindowIndex_eq_of_first
    (n start : ℕ) (increment : ℕ → ℝ)
    (hfirst : IsFirstSurvivingWindow n start increment) :
    firstSurvivingWindowIndex n increment = start := by
  have hex : ∃ j : ℕ,
      SurvivesNonnegative n (fun k => increment (j + k)) :=
    ⟨start, hfirst.1⟩
  exact (firstSurvivingWindowIndex_spec n increment hex).unique hfirst

/-- The first surviving-window index is measurable. -/
theorem measurable_firstSurvivingWindowIndex (n : ℕ) :
    Measurable (firstSurvivingWindowIndex n) := by
  classical
  let hasWindow : Set (ℕ → ℝ) :=
    {increment | ∃ start : ℕ,
      SurvivesNonnegative n (fun k => increment (start + k))}
  have hhasWindow : MeasurableSet hasWindow := by
    have hset : hasWindow = ⋃ start : ℕ,
        {increment : ℕ → ℝ |
          SurvivesNonnegative n (fun k => increment (start + k))} := by
      ext increment
      simp [hasWindow]
    rw [hset]
    exact MeasurableSet.iUnion fun start =>
      (measurableSet_survivesNonnegative n).preimage
        (measurable_natAdd start)
  refine measurable_to_nat fun increment => ?_
  let j := firstSurvivingWindowIndex n increment
  have hfiber :
      {x : ℕ → ℝ | firstSurvivingWindowIndex n x = j} =
        {x | IsFirstSurvivingWindow n j x ∨
          (j = 0 ∧ x ∉ hasWindow)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    by_cases hex : x ∈ hasWindow
    · have hspec := firstSurvivingWindowIndex_spec n x hex
      constructor
      · intro hidx
        exact Or.inl (by simpa [hidx] using hspec)
      · rintro (hfirst | ⟨_, hnot⟩)
        · exact firstSurvivingWindowIndex_eq_of_first n j x hfirst
        · exact False.elim (hnot hex)
    · have hidx : firstSurvivingWindowIndex n x = 0 := by
        change ¬ ∃ start : ℕ,
          SurvivesNonnegative n (fun k => x (start + k)) at hex
        simp [firstSurvivingWindowIndex, hex]
      have hnotFirst : ¬ IsFirstSurvivingWindow n j x := by
        intro hfirst
        exact hex ⟨j, hfirst.1⟩
      simp [hidx, hnotFirst, hex, eq_comm]
  change MeasurableSet {x : ℕ → ℝ |
    firstSurvivingWindowIndex n x = j}
  rw [hfiber]
  exact (measurableSet_isFirstSurvivingWindow n j).union
    (by by_cases hj : j = 0
        · simp only [hj, true_and]
          exact hhasWindow.compl
        · simp only [hj, false_and]
          exact MeasurableSet.empty)

/-- The increment block beginning at the first surviving-window index. -/
noncomputable def selectedFirstSurvivingBlock (n : ℕ)
    (increment : ℕ → ℝ) : Fin n → ℝ :=
  Combinatorics.Sequence.blockCoordinates
    (firstSurvivingWindowIndex n increment) n increment

/-- The selected finite increment block is a measurable random variable. -/
theorem measurable_selectedFirstSurvivingBlock (n : ℕ) :
    Measurable (selectedFirstSurvivingBlock n) := by
  have hjoint : Measurable
      (fun p : ℕ × (ℕ → ℝ) =>
        Combinatorics.Sequence.blockCoordinates p.1 n p.2) := by
    exact measurable_from_prod_countable_right fun start =>
      measurable_blockCoordinates start n
  exact hjoint.comp ((measurable_firstSurvivingWindowIndex n).prodMk
    measurable_id)

/-- The first surviving length-`n` block has the initial block's law
conditioned on survival. This is Lemma 3.1 as a law of finite blocks. -/
theorem measure_selectedFirstSurvivingBlock_eq_conditionalBlock
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (n : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
        ((selectedFirstSurvivingBlock n) ⁻¹' event) =
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          (event ∩ {block | FiniteSurvivesNonnegative block})) /
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block}) := by
  let μ := iidSequenceLaw ν
  let first : Set (ℕ → ℝ) :=
    ⋃ start : ℕ,
      {increment | IsFirstSurvivingWindow n start increment}
  have hfirstMeas : MeasurableSet first := by
    exact MeasurableSet.iUnion fun start =>
      measurableSet_isFirstSurvivingWindow n start
  have hfull : μ first = 1 :=
    measure_exists_firstSurvivingWindow_eq_one ν hpositive n
  have hfirstAE : ∀ᵐ increment ∂μ,
      ∃ start : ℕ, IsFirstSurvivingWindow n start increment := by
    filter_upwards [(mem_ae_iff_prob_eq_one hfirstMeas).mpr hfull]
      with increment hinc
    simpa only [first, Set.mem_iUnion, Set.mem_ofPred_eq] using hinc
  have hsetAE :
      (selectedFirstSurvivingBlock n) ⁻¹' event =ᵐ[μ]
        ⋃ start : ℕ,
          {increment | IsFirstSurvivingWindow n start increment} ∩
            (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event := by
    filter_upwards [hfirstAE] with increment ⟨start, hfirst⟩
    have hindex := firstSurvivingWindowIndex_eq_of_first
      n start increment hfirst
    have hblock : selectedFirstSurvivingBlock n increment =
        Combinatorics.Sequence.blockCoordinates start n increment := by
      simp [selectedFirstSurvivingBlock, hindex]
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    apply propext
    constructor
    · intro h
      exact ⟨start, hfirst, by rwa [hblock] at h⟩
    · rintro ⟨other, hother, hmem⟩
      have heq := hfirst.unique hother
      rw [← heq] at hmem
      rwa [hblock]
  calc
    μ ((selectedFirstSurvivingBlock n) ⁻¹' event) =
        μ (⋃ start : ℕ,
          {increment | IsFirstSurvivingWindow n start increment} ∩
            (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) :=
      measure_congr hsetAE
    _ = _ :=
      measure_firstWindow_block_union_eq_conditionalBlock
        ν hpositive n event hevent

/-- Equality of the selected block's law with the survival-conditioned
initial block law. This is the measure form of Bolthausen's Lemma 3.1. -/
theorem measure_map_selectedFirstSurvivingBlock_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0)) (n : ℕ) :
    (iidSequenceLaw ν).map (selectedFirstSurvivingBlock n) =
      (survivalConditionedLaw ν n).map
        (Combinatorics.Sequence.blockCoordinates 0 n) := by
  apply Measure.ext
  intro event hevent
  rw [Measure.map_apply (measurable_selectedFirstSurvivingBlock n) hevent,
    Measure.map_apply (measurable_blockCoordinates 0 n) hevent]
  rw [measure_selectedFirstSurvivingBlock_eq_conditionalBlock
    ν hpositive n event hevent]
  have hsurvive :
      {increment : ℕ → ℝ | SurvivesNonnegative n increment} =
        (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block} := by
    ext increment
    change SurvivesNonnegative n increment ↔
      FiniteSurvivesNonnegative
        (Combinatorics.Sequence.blockCoordinates 0 n increment)
    simpa only [zero_add] using
      (finiteSurvivesNonnegative_blockCoordinates_iff n 0 increment).symm
  rw [survivalConditionedLaw, ProbabilityTheory.cond_apply
    (measurableSet_survivesNonnegative n)]
  rw [hsurvive]
  have hinter :
      (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          {block | FiniteSurvivesNonnegative block} ∩
        (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' event =
      (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
        (event ∩ {block | FiniteSurvivesNonnegative block}) := by
    ext increment
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact and_comm
  rw [hinter]
  exact (div_eq_mul_inv _ _).trans (mul_comm _ _)

/-- The polygonal path of the first surviving block has the same law
as the initial polygonal path conditioned on survival. This is the
path-level consequence of Bolthausen's Lemma 3.1 used in Theorem 3.2. -/
theorem measure_map_selectedFirstSurvivingBlockPath_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (scale : ℕ → ℝ) (n : ℕ) :
    (iidSequenceLaw ν).map (fun increment =>
        normalizedLinearContinuousPathFromBlock scale n
          (selectedFirstSurvivingBlock n increment)) =
      (survivalConditionedLaw ν n).map
        (normalizedLinearContinuousPathIcc scale n) := by
  let path := normalizedLinearContinuousPathFromBlock scale n
  let block : (ℕ → ℝ) → Fin n → ℝ :=
    Combinatorics.Sequence.blockCoordinates 0 n
  have hblockLaw := measure_map_selectedFirstSurvivingBlock_eq
    ν hpositive n
  calc
    (iidSequenceLaw ν).map (fun increment =>
        path (selectedFirstSurvivingBlock n increment)) =
        ((iidSequenceLaw ν).map (selectedFirstSurvivingBlock n)).map
          path := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_normalizedLinearContinuousPathFromBlock
                scale n
            · exact measurable_selectedFirstSurvivingBlock n
    _ = ((survivalConditionedLaw ν n).map block).map path := by
          rw [hblockLaw]
    _ = (survivalConditionedLaw ν n).map (fun increment =>
          path (block increment)) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_normalizedLinearContinuousPathFromBlock
                scale n
            · exact measurable_blockCoordinates 0 n
    _ = (survivalConditionedLaw ν n).map
          (normalizedLinearContinuousPathIcc scale n) := by
            congr 1
            funext increment
            simpa only [zero_add] using
              (normalizedLinearContinuousPathFromBlock_blockCoordinates
                scale n 0 increment)

/-- Rebasing the polygonal walk at its selected discrete first-window
index gives the survival-conditioned unit-time polygonal path law. -/
theorem measure_map_rebasedAtFirstSurvivingWindow_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (iidSequenceLaw ν).map (fun increment =>
        restrictPathToUnitInterval
          (shiftToZero
            (normalizedLinearContinuousPathUnbounded scale n increment)
            (⟨(firstSurvivingWindowIndex n increment : ℝ) / n,
              div_nonneg (Nat.cast_nonneg (firstSurvivingWindowIndex n increment))
                (Nat.cast_nonneg n)⟩ : ℝ≥0))) =
      (survivalConditionedLaw ν n).map
        (normalizedLinearContinuousPathIcc scale n) := by
  have hpath (increment : ℕ → ℝ) :
      restrictPathToUnitInterval
          (shiftToZero
            (normalizedLinearContinuousPathUnbounded scale n increment)
            (⟨(firstSurvivingWindowIndex n increment : ℝ) / n,
              div_nonneg (Nat.cast_nonneg (firstSurvivingWindowIndex n increment))
                (Nat.cast_nonneg n)⟩ : ℝ≥0)) =
        normalizedLinearContinuousPathFromBlock scale n
          (selectedFirstSurvivingBlock n increment) := by
    exact restrictPathToUnitInterval_shiftToZero_grid scale hn
      (firstSurvivingWindowIndex n increment) increment
  calc
    (iidSequenceLaw ν).map (fun increment =>
        restrictPathToUnitInterval
          (shiftToZero
            (normalizedLinearContinuousPathUnbounded scale n increment)
            (⟨(firstSurvivingWindowIndex n increment : ℝ) / n,
              div_nonneg (Nat.cast_nonneg (firstSurvivingWindowIndex n increment))
                (Nat.cast_nonneg n)⟩ : ℝ≥0))) =
        (iidSequenceLaw ν).map (fun increment =>
          normalizedLinearContinuousPathFromBlock scale n
            (selectedFirstSurvivingBlock n increment)) := by
              congr 1
              funext increment
              exact hpath increment
    _ = _ := measure_map_selectedFirstSurvivingBlockPath_eq
      ν hpositive scale n

/-- On a walk with a surviving window, the centered continuous first-window
path is the polygonal path of its first surviving discrete block. -/
private theorem centeredFirstWindowShift_eq_selectedFirstSurvivingBlockPath
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) (increment : ℕ → ℝ)
    (hex : ∃ start : ℕ,
      SurvivesNonnegative n (fun k => increment (start + k))) :
    restrictPathToUnitInterval
        (centeredFirstWindowShift
          (normalizedLinearContinuousPathUnbounded scale n increment)) =
      normalizedLinearContinuousPathFromBlock scale n
        (selectedFirstSurvivingBlock n increment) := by
  have htime := firstNonnegativeWindowStart_eq_firstSurvivingWindowIndex
    scale hn hscale increment hex
  simp only [centeredFirstWindowShift, htime]
  simp
  exact restrictPathToUnitInterval_shiftToZero_grid scale hn
    (firstSurvivingWindowIndex n increment) increment

/-- Exact centered first-window path-law identity in Bolthausen's
equation (3.2), after identifying the continuous and lattice starts. -/
theorem measure_map_centeredFirstWindowShift_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpositive : 0 < ν (Set.Ioi 0))
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) :
    (iidSequenceLaw ν).map (fun increment =>
        restrictPathToUnitInterval
          (centeredFirstWindowShift
            (normalizedLinearContinuousPathUnbounded scale n increment))) =
      (survivalConditionedLaw ν n).map
        (normalizedLinearContinuousPathIcc scale n) := by
  let μ := iidSequenceLaw ν
  let first : Set (ℕ → ℝ) :=
    ⋃ start : ℕ,
      {increment | IsFirstSurvivingWindow n start increment}
  have hfirstMeas : MeasurableSet first :=
    MeasurableSet.iUnion fun start =>
      measurableSet_isFirstSurvivingWindow n start
  have hfull : μ first = 1 :=
    measure_exists_firstSurvivingWindow_eq_one ν hpositive n
  have hfirstAE : ∀ᵐ increment ∂μ,
      ∃ start : ℕ,
        SurvivesNonnegative n (fun k => increment (start + k)) := by
    filter_upwards [(mem_ae_iff_prob_eq_one hfirstMeas).mpr hfull]
      with increment hinc
    obtain ⟨start, hstart⟩ := by
      simpa only [first, Set.mem_iUnion, Set.mem_ofPred_eq] using hinc
    exact ⟨start, hstart.1⟩
  calc
    (iidSequenceLaw ν).map (fun increment =>
        restrictPathToUnitInterval
          (centeredFirstWindowShift
            (normalizedLinearContinuousPathUnbounded scale n increment))) =
        (iidSequenceLaw ν).map (fun increment =>
          normalizedLinearContinuousPathFromBlock scale n
            (selectedFirstSurvivingBlock n increment)) := by
              apply Measure.map_congr
              filter_upwards [hfirstAE] with increment hex
              exact centeredFirstWindowShift_eq_selectedFirstSurvivingBlockPath
                scale hn hscale increment hex
    _ = _ := measure_map_selectedFirstSurvivingBlockPath_eq
      ν hpositive scale n

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
