/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.Excursions
public import Probability.Process.RandomWalk.Path.Skorokhod
public import Topology.Cadlag.Skorokhod.Range

/-!
# Range bounds for random-walk step paths

The range condition itself belongs to the general càdlàg path layer. This
adapter identifies a range exit for a normalized random-walk step path with
an excursion among its finitely many partial sums, and transfers the event to
the corresponding path law.
-/

open MeasureTheory ProbabilityTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A normalized step path stays in a symmetric closed interval exactly when
all the partial sums through its terminal time do. This is the deterministic
finite-grid characterization underlying the range-exit probability bound. -/
theorem normalizedStepCadlagPathIcc_mem_rangeIn_closedInterval_iff_partialSumBounds
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {radius : ℝ} (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        CadlagPath.rangeIn (T := unitInterval) (Set.Icc (-radius) radius) ↔
      ∀ k : Fin (n + 1),
        |(scale n)⁻¹ * AdditivePath.displacement k.val increment| ≤ radius := by
  constructor
  · intro hpath k
    change ∀ t : unitInterval,
      normalizedStepCadlagPathIcc scale n increment t ∈ Set.Icc (-radius) radius at hpath
    have hk : k.val ≤ n := by omega
    let t : unitInterval := ⟨(k.val : ℝ) / n, by
      constructor
      · positivity
      · rw [div_le_one (by positivity)]
        exact_mod_cast hk⟩
    have hvalue := hpath t
    change -radius ≤ normalizedStepPath scale n increment ((k.val : ℝ) / n) ∧
      normalizedStepPath scale n increment ((k.val : ℝ) / n) ≤ radius at hvalue
    rw [normalizedStepPath_grid scale hn increment] at hvalue
    exact abs_le.mpr hvalue
  · intro hpartial t
    let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
    have hk : k ≤ n := natFloor_mul_le_of_mem_unitInterval n t
    let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    have hvalue := hpartial j
    rw [Set.mem_Icc]
    simpa [normalizedStepCadlagPathIcc_apply, normalizedStepPath, j, k] using
      abs_le.mp hvalue

/-- If a normalized step path leaves a symmetric closed interval, one of its
nonempty partial sums reaches the corresponding unnormalized threshold. -/
theorem not_mem_rangeIn_closedInterval_subset_blockPrefixExceedance
    (scale : ℕ → ℝ) {n : ℕ}
    {radius : ℝ} (hradius : 0 < radius) (hscale : 0 < scale n)
    (increment : ℕ → ℝ) :
    (normalizedStepCadlagPathIcc scale n increment ∉
      CadlagPath.rangeIn (T := unitInterval) (Set.Icc (-radius) radius)) →
      increment ∈ blockPrefixExceedance 0 n (radius * scale n) := by
  intro hnot
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    apply hnot
    change ∀ t : unitInterval,
      normalizedStepCadlagPathIcc scale 0 increment t ∈ Set.Icc (-radius) radius
    intro t
    rw [normalizedStepCadlagPathIcc_apply]
    simp [normalizedStepPath, AdditivePath.displacement_zero, hradius.le]
  have hpartialNotAll : ¬ ∀ k : Fin (n + 1),
      |(scale n)⁻¹ * AdditivePath.displacement k.val increment| ≤ radius := by
    intro hpartial
    exact hnot <|
      (normalizedStepCadlagPathIcc_mem_rangeIn_closedInterval_iff_partialSumBounds
        scale hn (radius := radius) increment).2 hpartial
  obtain ⟨k, hk⟩ := not_forall.mp hpartialNotAll
  have hvalue : radius <
      |(scale n)⁻¹ * AdditivePath.displacement k.val increment| := not_le.mp hk
  have hk0 : k.val ≠ 0 := by
    intro hk0
    have hzero : AdditivePath.displacement k.val increment = 0 := by
      simp [hk0, AdditivePath.displacement]
    rw [hzero] at hvalue
    simp at hvalue
    linarith
  have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk0
  have hraw : radius * scale n < |AdditivePath.displacement k.val increment| := by
    have hmul : radius < (scale n)⁻¹ *
        |AdditivePath.displacement k.val increment| := by
      simpa [abs_mul, abs_of_pos (inv_pos.mpr hscale)] using hvalue
    calc
      radius * scale n <
          ((scale n)⁻¹ * |AdditivePath.displacement k.val increment|) * scale n :=
        mul_lt_mul_of_pos_right hmul hscale
      _ = |AdditivePath.displacement k.val increment| := by
        field_simp
  let j : Fin n := ⟨k.val - 1, by omega⟩
  have hj : j.val + 1 = k.val := by
    dsimp [j]
    omega
  refine ⟨j, ?_⟩
  rw [hj, AdditivePath.blockSum_eq_displacement_natAdd]
  simpa using hraw.le

/-- The law of a normalized step path assigns to a range-exit event no more
mass than the probability of the corresponding partial-sum excursion. -/
theorem measure_normalizedStepPathLaw_rangeIn_closedInterval_compl_le_of_blockPrefixExceedance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (scale : ℕ → ℝ) (n : ℕ)
    {radius : ℝ} (hradius : 0 < radius) (hscale : 0 < scale n)
    (bound : ENNReal)
    (hbound : (iidSequenceLaw ν)
      (blockPrefixExceedance 0 n (radius * scale n)) ≤ bound) :
    normalizedStepPathLaw ν scale n
        (CadlagPath.rangeIn (T := unitInterval) (Set.Icc (-radius) radius))ᶜ ≤ bound := by
  have hmeas : MeasurableSet
      (CadlagPath.rangeIn (T := unitInterval) (Set.Icc (-radius) radius)) :=
    Skorokhod.measurableSet_rangeIn isClosed_Icc
  have hsubset :
      normalizedStepCadlagPathIcc scale n ⁻¹'
          (CadlagPath.rangeIn (T := unitInterval) (Set.Icc (-radius) radius))ᶜ ⊆
        blockPrefixExceedance 0 n (radius * scale n) := by
    intro increment hexit
    exact not_mem_rangeIn_closedInterval_subset_blockPrefixExceedance
      scale hradius hscale increment hexit
  rw [normalizedStepPathLaw, Measure.map_apply]
  · exact (measure_mono hsubset).trans
      (by simpa [independentIncrementLaw] using hbound)
  · exact measurable_normalizedStepCadlagPathIcc scale n
  · exact hmeas.compl

end ProbabilityTheory.RandomWalk

end
