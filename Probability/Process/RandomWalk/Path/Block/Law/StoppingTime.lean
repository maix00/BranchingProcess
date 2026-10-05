/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Filtration
public import Probability.Process.RandomWalk.Path.Block.Law.Excursions
public import Mathlib.Probability.Process.Stopping

/-!
# Excursions after a discrete stopping time

For an IID increment path, a fixed finite block after a stopping time has the
same excursion bound as a deterministic block. The proof splits according to
the stopping-time value and uses independence of each future coordinate block
from the already observed increment prefix.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A finite-prefix excursion beginning at the random time `τ`. Infinite
stopping times contribute no event. -/
def blockPrefixExceedanceAfter
    (τ : (ℕ → ℝ) → WithTop ℕ) (length : ℕ) (threshold : ℝ) : Set (ℕ → ℝ) :=
  ⋃ n : ℕ, {path | τ path = n} ∩
    blockPrefixExceedance n length threshold

theorem measurableSet_blockPrefixExceedance
    (start length : ℕ) (threshold : ℝ) :
    MeasurableSet (blockPrefixExceedance start length threshold) := by
  rw [← blockPrefixExceedance_eq_preimage_blockCoordinates]
  exact (measurableSet_blockPrefixExceedanceOnCoordinates length threshold).preimage
    (blockCoordinates_measurable start length)

/-- At every deterministic time `n`, the stopping-time cell intersected with
the excursion of the next `length` increments factors into its past and
future probabilities. -/
theorem measure_stoppingTimeCell_inter_blockPrefixExceedance_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : (ℕ → ℝ) → WithTop ℕ)
    (hτ : IsStoppingTime (incrementFiltration (E := ℝ)) τ)
    (n length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν)
        ({path | τ path = n} ∩ blockPrefixExceedance n length threshold) =
      (iidSequenceLaw ν) {path | τ path = n} *
        (iidSequenceLaw ν) (blockPrefixExceedance n length threshold) := by
  let past := AdditivePath.blockCoordinates (E := ℝ) 0 n
  let future := AdditivePath.blockCoordinates (E := ℝ) n length
  let futureEvent := blockPrefixExceedanceOnCoordinates length threshold
  have hindep := indepFun_blockCoordinates_blockCoordinates ν 0 n length
  have hpastEqPrefix : past = incrementPrefix n := by
    funext path k
    simp [past, incrementPrefix, AdditivePath.blockCoordinates]
  have hpastMeasurable : MeasurableSet[MeasurableSpace.comap past inferInstance]
      {path | τ path = n} := by
    rw [hpastEqPrefix, ← incrementFiltration_eq_comap_incrementPrefix]
    exact hτ.measurableSet_eq n
  have hfutureMeasurable : MeasurableSet futureEvent :=
    measurableSet_blockPrefixExceedanceOnCoordinates length threshold
  obtain ⟨pastEvent, hpastEvent, hpastPreimage⟩ :=
    (MeasurableSpace.measurableSet_comap).1 hpastMeasurable
  have hfactor := hindep.measure_inter_preimage_eq_mul
    pastEvent futureEvent hpastEvent hfutureMeasurable
  have hfuturePreimage : future ⁻¹' futureEvent =
      blockPrefixExceedance n length threshold := by
    exact blockPrefixExceedance_eq_preimage_blockCoordinates n length threshold
  simpa only [past, future, Nat.zero_add, hpastPreimage, hfuturePreimage] using hfactor

/-- A bounded excursion immediately after any discrete stopping time has
probability at most the corresponding deterministic block probability. -/
theorem measure_blockPrefixExceedanceAfter_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : (ℕ → ℝ) → WithTop ℕ)
    (hτ : IsStoppingTime (incrementFiltration (E := ℝ)) τ)
    (length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν) (blockPrefixExceedanceAfter τ length threshold) ≤
      (iidSequenceLaw ν) (blockPrefixExceedance 0 length threshold) := by
  let μ := iidSequenceLaw ν
  let cell : ℕ → Set (ℕ → ℝ) := fun n => {path | τ path = n}
  let excursion : ℕ → Set (ℕ → ℝ) := fun n =>
    blockPrefixExceedance n length threshold
  have hcellMeasurable (n : ℕ) : MeasurableSet (cell n) :=
    (incrementFiltration (E := ℝ)).le n _ (hτ.measurableSet_eq n)
  have hexcursionMeasurable (n : ℕ) : MeasurableSet (excursion n) :=
    measurableSet_blockPrefixExceedance n length threshold
  have hcellPairwise : Pairwise (fun i j => Disjoint (cell i) (cell j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro path hi hj
    exact hij (WithTop.coe_injective (hi.symm.trans hj))
  have hunionCells : (⋃ n, cell n) = {path | τ path ≠ ⊤} := by
    ext path
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      rw [hn]
      exact WithTop.coe_ne_top
    · intro hfinite
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
      exact ⟨n, hn.symm⟩
  have hcellTsum : ∑' n, μ (cell n) = μ {path | τ path ≠ ⊤} := by
    rw [← hunionCells]
    exact (measure_iUnion hcellPairwise hcellMeasurable).symm
  have hcellBound : ∑' n, μ (cell n) ≤ 1 := by
    calc
      ∑' n, μ (cell n) = μ {path | τ path ≠ ⊤} := hcellTsum
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hcellFactor (n : ℕ) :
      μ (cell n ∩ excursion n) = μ (cell n) * μ (excursion 0) := by
    rw [show μ (cell n ∩ excursion n) =
        μ (cell n) * μ (excursion n) by
      simpa [μ, cell, excursion] using
        measure_stoppingTimeCell_inter_blockPrefixExceedance_eq_mul
          ν τ hτ n length threshold]
    rw [show μ (excursion n) = μ (excursion 0) by
      simpa [μ, excursion, Nat.add_zero] using
        (measure_blockPrefixExceedance_translate_eq ν n 0 length threshold)]
  have hunion : blockPrefixExceedanceAfter τ length threshold =
      ⋃ n, cell n ∩ excursion n := rfl
  calc
    μ (blockPrefixExceedanceAfter τ length threshold) =
        μ (⋃ n, cell n ∩ excursion n) := by rw [hunion]
    _ ≤ ∑' n, μ (cell n ∩ excursion n) := measure_iUnion_le _
    _ = ∑' n, μ (cell n) * μ (excursion 0) := tsum_congr hcellFactor
    _ = (∑' n, μ (cell n)) * μ (excursion 0) := ENNReal.tsum_mul_right
    _ ≤ 1 * μ (excursion 0) := by
      exact mul_le_mul_of_nonneg_right hcellBound (by positivity)
    _ = μ (excursion 0) := one_mul _

end ProbabilityTheory.RandomWalk

end
