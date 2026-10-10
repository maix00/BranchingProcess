/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.NormingRatios.Index
public import Probability.Distributions.Stable.Convolution
public import Probability.Process.Path.UnitInterval
public import Probability.Process.RandomWalk.FunctionalLimit.FiniteDimensional.IndependentBlocks
public import Probability.Process.RandomWalk.Path.Scaling

/-!
# Source finite-dimensional limits on stable random-walk grids

This file identifies the limiting grid-increment law directly from the
domain-of-attraction input. It does not assume an already constructed stable
process or a path-space functional limit theorem.
-/

open Filter MeasureTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- The integer time sampled by a unit-interval grid in the length-`n`
random walk. -/
noncomputable def unitIntervalGridFloorTime {blocks : ℕ}
    (grid : Fin (blocks + 1) → unitInterval) (n : ℕ)
    (j : Fin (blocks + 1)) : ℕ :=
  ⌊(n : ℝ) * (grid j : ℝ)⌋₊

/-- The number of random-walk increments between the two floored endpoints
of a grid interval. -/
noncomputable def unitIntervalGridBlockLength {blocks : ℕ}
    (grid : Fin (blocks + 1) → unitInterval) (n j : ℕ) : ℕ :=
  if hj : j < blocks then
    unitIntervalGridFloorTime grid n (Fin.succ ⟨j, hj⟩) -
      unitIntervalGridFloorTime grid n (Fin.castSucc ⟨j, hj⟩)
  else 0

/-- For a valid block index, the grid block length is the difference of the
two floored endpoint times. -/
theorem unitIntervalGridBlockLength_eq {blocks : ℕ}
    (grid : Fin (blocks + 1) → unitInterval) (n : ℕ) (j : Fin blocks) :
    unitIntervalGridBlockLength grid n j.val =
      unitIntervalGridFloorTime grid n j.succ -
        unitIntervalGridFloorTime grid n j.castSucc := by
  simp [unitIntervalGridBlockLength, j.isLt]

/-- The cumulative length of the first grid blocks reaches the floored time
at the corresponding grid point. -/
theorem unitIntervalGridBlockStart_eq_floorTime {blocks : ℕ}
    (grid : Fin (blocks + 1) → unitInterval) (n : ℕ)
    (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
    ∀ j : Fin (blocks + 1),
      AdditivePath.blockStart (unitIntervalGridBlockLength grid n) j.val =
        unitIntervalGridFloorTime grid n j := by
  intro j
  induction j using Fin.induction with
  | zero => simp [AdditivePath.blockStart, unitIntervalGridFloorTime, hstart]
  | succ j ih =>
      have ih' : AdditivePath.blockStart (unitIntervalGridBlockLength grid n)
          j.val = unitIntervalGridFloorTime grid n j.castSucc := by
        simpa only [Fin.val_castSucc] using ih
      simp only [Fin.val_succ, AdditivePath.blockStart_succ]
      rw [ih', unitIntervalGridBlockLength_eq]
      have hfloorLe : unitIntervalGridFloorTime grid n j.castSucc ≤
          unitIntervalGridFloorTime grid n j.succ := by
        apply Nat.floor_mono
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast hgrid.monotone (Fin.castSucc_le_succ j)
        · exact_mod_cast (Nat.zero_le n : 0 ≤ n)
      exact Nat.add_sub_of_le hfloorLe

/-- The product probability measure whose coordinates are the stable laws at
the successive durations of a unit-interval grid. -/
noncomputable def stableTimeLawProductProbability {blocks : ℕ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (α : ℝ)
    (grid : Fin (blocks + 1) → unitInterval) :
    ProbabilityMeasure (Fin blocks → ℝ) := by
  let coordinateLaw : Fin blocks → Measure ℝ := fun j =>
    stableTimeLaw α μ ((grid j.succ : ℝ) - (grid j.castSucc : ℝ))
  have hcoordinate (j : Fin blocks) : IsProbabilityMeasure (coordinateLaw j) := by
    dsimp [coordinateLaw, stableTimeLaw]
    infer_instance
  letI : ∀ j : Fin blocks, IsProbabilityMeasure (coordinateLaw j) := hcoordinate
  exact ⟨Measure.pi coordinateLaw, inferInstance⟩

private theorem tendsto_natFloor_mul_div_unitInterval (t : unitInterval) :
    Tendsto (fun n : ℕ =>
      (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / (n : ℝ)) atTop (𝓝 (t : ℝ)) := by
  by_cases ht : (t : ℝ) = 0
  · have heq : (fun n : ℕ =>
        (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / (n : ℝ)) = fun _ => 0 := by
      funext n
      simp [ht]
    rw [heq]
    simp [ht]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    let argument : ℕ → ℝ := fun n => (t : ℝ) * (n : ℝ)
    have hargument : Tendsto argument atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop htpos
    have hfloor : Tendsto (fun n : ℕ =>
        (⌊argument n⌋₊ : ℝ) / argument n) atTop (𝓝 1) :=
      (tendsto_nat_floor_div_atTop (R := ℝ)).comp hargument
    have hratio : Tendsto (fun n : ℕ => argument n / (n : ℝ)) atTop
        (𝓝 (t : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      dsimp [argument]
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
    have hproduct : Tendsto (fun n : ℕ =>
        ((⌊argument n⌋₊ : ℝ) / argument n) * (argument n / (n : ℝ)))
        atTop (𝓝 (1 * (t : ℝ))) := hfloor.mul hratio
    have heq : (fun n : ℕ =>
        ((⌊argument n⌋₊ : ℝ) / argument n) * (argument n / (n : ℝ))) =ᶠ[atTop]
        fun n => (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / (n : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have harg0 : argument n ≠ 0 := by
        dsimp [argument]
        exact mul_ne_zero (ne_of_gt htpos) hn0
      calc
        ((⌊argument n⌋₊ : ℝ) / argument n) * (argument n / (n : ℝ)) =
            (⌊argument n⌋₊ : ℝ) / (n : ℝ) := by field_simp
        _ = (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) / (n : ℝ) := by
          have harg : argument n = (n : ℝ) * (t : ℝ) := by
            dsimp [argument]
            ring
          rw [harg]
    simpa using (hproduct.congr' heq)

/-- The increments of a normalized random walk on a finite, strictly
increasing unit-interval grid converge directly to the product of the stable
time laws of the grid intervals. The only path-specific input is the
vanishing of the deterministic centering on each grid block. The conclusion
is stated as convergence to the identity random variable under the product
measure; no stable process witness is used to represent that measure.
-/
theorem tendstoInDistribution_normalizedStepPath_finiteGrid_increments_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hStable : IsStrictlyAlphaStable α μ)
    (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : StrictMono grid)
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n : ℕ => center
        (⌊(n : ℝ) * (grid j.succ : ℝ)⌋₊ -
          ⌊(n : ℝ) * (grid j.castSucc : ℝ)⌋₊) / normalization n)
        atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart
          (unitIntervalGridBlockLength grid n) j.val)
          (unitIntervalGridBlockLength grid n j.val) increments / normalization n)
      atTop id
      (fun _ => iidSequenceLaw ν)
      (stableTimeLawProductProbability (μ := μ) α grid : Measure (Fin blocks → ℝ)) := by
  let floorTime := unitIntervalGridFloorTime grid
  let length := unitIntervalGridBlockLength grid
  have hlength_eq (n : ℕ) (j : Fin blocks) :
      length n j.val = floorTime n j.succ - floorTime n j.castSucc := by
    simp [length, floorTime, unitIntervalGridBlockLength,
      unitIntervalGridFloorTime, j.isLt]
  have hlengthRatio (j : Fin blocks) :
      Tendsto (fun n => (length n j.val : ℝ) / (n : ℝ)) atTop
        (𝓝 ((grid j.succ : ℝ) - (grid j.castSucc : ℝ))) := by
    have hupper := tendsto_natFloor_mul_div_unitInterval (grid j.succ)
    have hlower := tendsto_natFloor_mul_div_unitInterval (grid j.castSucc)
    have hdiff := hupper.sub hlower
    have hfloorLe (n : ℕ) : floorTime n j.castSucc ≤ floorTime n j.succ := by
      apply Nat.floor_mono
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast (hgrid.monotone (Fin.castSucc_le_succ j))
      · exact_mod_cast (Nat.zero_le n : 0 ≤ n)
    have hcast (n : ℕ) :
        (length n j.val : ℝ) =
          (floorTime n j.succ : ℝ) - (floorTime n j.castSucc : ℝ) := by
      rw [hlength_eq n j]
      exact_mod_cast Nat.cast_sub (hfloorLe n)
    have heq : (fun n : ℕ => (length n j.val : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => (floorTime n j.succ : ℝ) / (n : ℝ) -
          (floorTime n j.castSucc : ℝ) / (n : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hcast n]
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      ring
    simpa [floorTime, unitIntervalGridFloorTime] using hdiff.congr' heq.symm
  have hblock (j : Fin blocks) :
      Tendsto (fun n => length n j.val) atTop atTop := by
    have hduration : 0 < (grid j.succ : ℝ) - (grid j.castSucc : ℝ) :=
      sub_pos.mpr (by exact_mod_cast hgrid Fin.castSucc_lt_succ)
    have hratio := hlengthRatio j
    have hnear : ∀ᶠ n : ℕ in atTop,
        (((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) / 2) <
          (length n j.val : ℝ) / (n : ℝ) :=
      hratio.eventually (Ioi_mem_nhds (by linarith))
    have hlinear : Tendsto (fun n : ℕ =>
        (((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) / 2) * (n : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    have hbound : ∀ᶠ n : ℕ in atTop,
        (((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) / 2) * (n : ℝ) ≤
          (length n j.val : ℝ) := by
      filter_upwards [hnear, eventually_gt_atTop 0] with n hratio hn
      have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hmul := (lt_div_iff₀ hnReal).1 hratio
      linarith
    have hlengthReal : Tendsto (fun n : ℕ => (length n j.val : ℝ))
        atTop atTop := tendsto_atTop_mono' atTop hbound hlinear
    apply tendsto_atTop.2
    intro k
    filter_upwards [tendsto_atTop.1 hlengthReal (k : ℝ)] with n hn
    exact_mod_cast hn
  have hspatial : ∀ᶠ n in atTop, normalization n ≠ 0 :=
    hDOA.eventually_scale_pos.mono fun _ hn => hn.ne'
  let ratio : Fin blocks → ℝ := fun j =>
    ((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) ^ (1 / α)
  have hratio (j : Fin blocks) :
      Tendsto (fun n => normalization (length n j.val) / normalization n)
        atTop (𝓝 (ratio j)) := by
    have hpositive : 0 < (grid j.succ : ℝ) - (grid j.castSucc : ℝ) :=
      sub_pos.mpr (by exact_mod_cast hgrid Fin.castSucc_lt_succ)
    have h := IsInDomainOfAttractionAlong.tendsto_norming_ratio
      hStable.isAlphaStable hDOA (fun n => length n j.val)
      ((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) hpositive (hlengthRatio j)
    simpa [ratio, one_div] using h
  have hcenter' (j : Fin blocks) :
      Tendsto (fun n => center (length n j.val) / normalization n)
        atTop (𝓝 0) := by
    have heq : (fun n : ℕ => center (length n j.val) / normalization n) =ᶠ[atTop]
        fun n => center (floorTime n j.succ - floorTime n j.castSucc) /
          normalization n := by
      filter_upwards [] with n
      rw [hlength_eq n j]
    exact (hcenter j).congr' heq.symm
  have hblocks :=
    tendstoInDistribution_consecutiveBlockSums hDOA blocks length normalization
      ratio (fun _ => 0) hblock hspatial hratio hcenter'
  let scaledVector : (Fin blocks → ℝ) → Fin blocks → ℝ :=
    fun z j => ratio j * z j
  let targetLaw : Measure (Fin blocks → ℝ) :=
    stableTimeLawProductProbability (μ := μ) α grid
  have hscaledPi :
      (Measure.pi fun _ : Fin blocks => μ).map scaledVector = targetLaw := by
    have hpi := Measure.pi_map_pi
      (fun j : Fin blocks =>
        (by fun_prop : AEMeasurable (fun x : ℝ => ratio j * x) μ))
    simpa [targetLaw, scaledVector, stableTimeLaw, ratio,
      stableTimeLawProductProbability] using hpi
  have hmap :
      (Measure.pi fun _ : Fin blocks => μ).map
        (fun z j => ratio j * z j + (0 : ℝ)) = targetLaw.map id := by
    rw [Measure.map_id]
    convert hscaledPi using 1
    ext z j
    simp [scaledVector]
  have hblocks' : TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin blocks) =>
        AdditivePath.blockSum (AdditivePath.blockStart (length n) j.val)
          (length n j.val) increments / normalization n)
      atTop id (fun _ => iidSequenceLaw ν) targetLaw := by
    simpa [targetLaw, length, floorTime, unitIntervalGridBlockLength,
      unitIntervalGridFloorTime, stableTimeLawProductProbability] using
      (hblocks.congr_limit (aemeasurable_id : AEMeasurable id targetLaw) hmap)
  exact hblocks'

/-- The normalized source step path has the finite-dimensional position law
obtained by summing the independent stable time-increment laws on the grid.
This formulation uses only the scalar domain-of-attraction hypothesis and
strict stability; it does not assume a stable process witness. -/
theorem tendstoInDistribution_normalizedStepPath_finiteGrid_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hStable : IsStrictlyAlphaStable α μ)
    (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : StrictMono grid) (hstart : grid 0 = ⊥)
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n : ℕ => center
        (unitIntervalGridFloorTime grid n j.succ -
          unitIntervalGridFloorTime grid n j.castSucc) / normalization n)
        atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        RandomWalk.normalizedStepPath normalization n increments (grid j : ℝ))
      atTop id
      (fun _ => iidSequenceLaw ν)
      ((stableTimeLawProductProbability (μ := μ) α grid).map
        (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)) := by
  let length := unitIntervalGridBlockLength grid
  let incrementVector : ℕ → (ℕ → ℝ) → Fin blocks → ℝ := fun n increments j =>
    AdditivePath.blockSum (AdditivePath.blockStart (length n) j.val)
      (length n j.val) increments / normalization n
  let partialSumMap : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ := Fin.partialSum
  have hinc := tendstoInDistribution_normalizedStepPath_finiteGrid_increments_of_stableDomain
    hDOA hStable blocks grid hgrid hcenter
  have hpartial := hinc.continuous_comp (Fin.continuous_partialSum blocks)
  have hscale (n : ℕ) (increments : ℕ → ℝ) (j : Fin (blocks + 1)) :
      Fin.partialSum (fun k : Fin blocks => incrementVector n increments k) j =
        Fin.partialSum (fun k : Fin blocks =>
          AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
            (length n k.val) increments) j / normalization n := by
    calc
      _ = Fin.partialSum (fun k : Fin blocks =>
          (normalization n)⁻¹ * AdditivePath.blockSum
            (AdditivePath.blockStart (length n) k.val) (length n k.val)
            increments) j := by
          congr 1
          funext k
          simp [incrementVector, div_eq_mul_inv, mul_comm]
      _ = (normalization n)⁻¹ * Fin.partialSum (fun k : Fin blocks =>
          AdditivePath.blockSum (AdditivePath.blockStart (length n) k.val)
            (length n k.val) increments) j := by
          simpa [smul_eq_mul] using
            (Fin.partialSum_smul (R := ℝ) (M := ℝ) ((normalization n)⁻¹)
              (fun k : Fin blocks => AdditivePath.blockSum
                (AdditivePath.blockStart (length n) k.val) (length n k.val)
                increments) j)
      _ = _ := by simp [div_eq_mul_inv, mul_comm]
  have hpath (n : ℕ) (increments : ℕ → ℝ) :
      (fun j : Fin (blocks + 1) =>
        RandomWalk.normalizedStepPath normalization n increments (grid j : ℝ)) =
      fun j => partialSumMap (incrementVector n increments) j := by
    funext j
    dsimp [partialSumMap]
    change (normalization n)⁻¹ * AdditivePath.displacement
      (unitIntervalGridFloorTime grid n j) increments = _
    rw [← unitIntervalGridBlockStart_eq_floorTime grid n hgrid hstart j]
    rw [← ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.partialSum_variableBlockSums
      (length n) increments j]
    rw [hscale n increments j]
    simp [div_eq_mul_inv, mul_comm]
  let targetLaw : ProbabilityMeasure (Fin blocks → ℝ) :=
    stableTimeLawProductProbability (μ := μ) α grid
  let positionLaw : ProbabilityMeasure (Fin (blocks + 1) → ℝ) :=
    targetLaw.map
      (Fin.partialSum : (Fin blocks → ℝ) → Fin (blocks + 1) → ℝ)
  have hposition : TendstoInDistribution
      (fun n increments => Fin.partialSum (incrementVector n increments))
      atTop id (fun _ => iidSequenceLaw ν)
      positionLaw := by
    apply hpartial.congr_limit (aemeasurable_id : AEMeasurable id positionLaw)
    simp [positionLaw, targetLaw]
  simpa [positionLaw, targetLaw] using hposition.congr_eventually
    (Filter.Eventually.of_forall fun n =>
      Filter.Eventually.of_forall fun increments => (hpath n increments).symm)
    (fun n => (Measurable.of_eval fun j : Fin (blocks + 1) =>
      RandomWalk.normalizedStepPath_measurable normalization n (grid j : ℝ)).aemeasurable)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
