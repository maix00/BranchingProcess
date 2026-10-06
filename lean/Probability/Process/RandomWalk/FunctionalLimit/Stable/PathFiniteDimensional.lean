/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.UnitInterval
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.FiniteDimensional
public import Probability.Process.RandomWalk.Path.Scaling

/-!
# Finite-dimensional limits of stable random-walk paths

The endpoint-vector stable domain-of-attraction theorem also gives convergence
of the normalized step path at any finite grid whose integer block endpoints
agree with the path's floor-time evaluations. The block-scale and centering
limits are explicit inputs, just as in the endpoint theorem.
-/

open Filter MeasureTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

variable {Ω : Type*} [MeasurableSpace Ω]

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

/-- Finite-dimensional convergence at any strictly increasing real-time grid.
The grid is converted to consecutive blocks using `⌊nt⌋`; all block-length,
norming, and centering limits are discharged here, with the centered block
ratio left as an explicit hypothesis. -/
theorem tendstoInDistribution_normalizedStepPath_finiteGrid_floor_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {X : unitInterval → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hX : HasStableClockIncrements α μ unitIntervalClock X P)
    (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : StrictMono grid) (hgridStart : grid 0 = ⊥)
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n : ℕ => center
        (⌊(n : ℝ) * (grid j.succ : ℝ)⌋₊ -
          ⌊(n : ℝ) * (grid j.castSucc : ℝ)⌋₊) / normalization n)
        atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        normalizedStepPath normalization n increments (grid j : ℝ))
      atTop
      (fun ω j => X (grid j) ω)
      (fun _ => iidSequenceLaw ν) P := by
  let floorTime (n : ℕ) (j : Fin (blocks + 1)) : ℕ :=
    ⌊(n : ℝ) * (grid j : ℝ)⌋₊
  let length : ℕ → ℕ → ℕ := fun n j =>
    if hj : j < blocks then
      floorTime n (Fin.succ ⟨j, hj⟩) - floorTime n (Fin.castSucc ⟨j, hj⟩)
    else 0
  have hlength_eq (n : ℕ) (j : Fin blocks) :
      length n j.val = floorTime n j.succ - floorTime n j.castSucc := by
    simp only [length, dite_eq_left j.isLt]
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
    simpa [floorTime] using hdiff.congr' heq.symm
  have hblock (j : Fin blocks) :
      Tendsto (fun n => length n j.val) atTop atTop := by
    have hduration : 0 < (grid j.succ : ℝ) - (grid j.castSucc : ℝ) :=
      sub_pos.mpr (by exact_mod_cast hgrid Fin.castSucc_lt_succ)
    have hratio := hlengthRatio j
    have hnear : ∀ᶠ n : ℕ in atTop,
        ( ((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) / 2) <
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
  have hratio (j : Fin blocks) :
      Tendsto (fun n => normalization (length n j.val) / normalization n)
        atTop (𝓝 (((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) ^ (1 / α))) := by
    have hpositive : 0 < (grid j.succ : ℝ) - (grid j.castSucc : ℝ) :=
      sub_pos.mpr (by exact_mod_cast hgrid Fin.castSucc_lt_succ)
    have h := IsInDomainOfAttractionAlong.tendsto_norming_ratio
      hX.strictlyStable.isAlphaStable hDOA (fun n => length n j.val)
      ((grid j.succ : ℝ) - (grid j.castSucc : ℝ)) hpositive (hlengthRatio j)
    simpa [one_div] using h
  have hposition (n : ℕ) (j : Fin (blocks + 1)) :
      AdditivePath.blockStart (length n) j.val = floorTime n j := by
    induction j using Fin.induction with
    | zero =>
        simp [AdditivePath.blockStart, floorTime, hgridStart]
    | succ j ih =>
        have ih' : AdditivePath.blockStart (length n) j.val =
            floorTime n j.castSucc := by
          simpa only [Fin.val_castSucc] using ih
        simp only [Fin.val_succ, AdditivePath.blockStart_succ]
        rw [ih']
        rw [hlength_eq n j]
        have hfloorLe : floorTime n j.castSucc ≤ floorTime n j.succ := by
          apply Nat.floor_mono
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast (hgrid.monotone (Fin.castSucc_le_succ j))
          · exact_mod_cast (Nat.zero_le n : 0 ≤ n)
        exact Nat.add_sub_of_le hfloorLe
  have hcenter' (j : Fin blocks) :
      Tendsto (fun n => center (length n j.val) / normalization n) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => center (length n j.val) / normalization n) =ᶠ[atTop]
        fun n => center (floorTime n j.succ - floorTime n j.castSucc) /
          normalization n := by
      filter_upwards [] with n
      rw [hlength_eq n j]
    exact (hcenter j).congr' heq.symm
  have hclockPositive (j : Fin blocks) :
      0 < unitIntervalClock (grid j.succ) - unitIntervalClock (grid j.castSucc) := by
    change 0 < (grid j.succ : ℝ) - (grid j.castSucc : ℝ)
    apply sub_pos.mpr
    exact_mod_cast (hgrid Fin.castSucc_lt_succ)
  have hendpoints := tendstoInDistribution_endpoints_of_stableNorming
    hDOA hX blocks grid hgrid.monotone hgridStart length hblock
    hlengthRatio hclockPositive hcenter'
  apply hendpoints.congr
  · intro n
    filter_upwards [] with increments
    funext j
    simp only [normalizedStepPath, hposition]
    rw [div_eq_mul_inv, mul_comm]
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- The floor-grid finite-dimensional limit needs no separate block-centering
input when the one-dimensional attraction statement itself uses zero
centering, as in the uncentered source convention. -/
theorem tendstoInDistribution_normalizedStepPath_finiteGrid_floor_of_zeroCenter
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {X : unitInterval → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hX : HasStableClockIncrements α μ unitIntervalClock X P)
    (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : StrictMono grid) (hgridStart : grid 0 = ⊥) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        normalizedStepPath normalization n increments (grid j : ℝ))
      atTop
      (fun ω j => X (grid j) ω)
      (fun _ => iidSequenceLaw ν) P := by
  apply tendstoInDistribution_normalizedStepPath_finiteGrid_floor_of_stableDomain
    (center := fun _ => 0) hDOA hX blocks grid hgrid hgridStart
  intro j
  simp

/-- Finite-dimensional convergence of the normalized right-continuous step
path, obtained by identifying its values with the cumulative endpoints of a
finite block decomposition. The block decomposition and all asymptotic scale
and centering hypotheses are part of the statement, so this result does not
silently assume positive block durations or negligible centering.
-/
theorem tendstoInDistribution_normalizedStepPath_finiteGrid_of_stableClock
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {X : unitInterval → Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P] {normalization center : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hX : HasStableClockIncrements α μ unitIntervalClock X P)
    (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
    (hgrid : Monotone grid) (hgridStart : grid 0 = ⊥)
    (length : ℕ → ℕ → ℕ) (spatialScale : ℕ → ℝ)
    (hblock : ∀ j : Fin blocks,
      Tendsto (fun n => length n j.val) atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : ∀ j : Fin blocks,
      Tendsto (fun n => normalization (length n j.val) / spatialScale n)
        atTop (nhds ((unitIntervalClock (grid j.succ) -
          unitIntervalClock (grid j.castSucc)) ^ (1 / α))))
    (hcenter : ∀ j : Fin blocks,
      Tendsto (fun n => center (length n j.val) / spatialScale n)
        atTop (nhds 0))
    (hposition : ∀ (n : ℕ) (j : Fin (blocks + 1)),
      AdditivePath.blockStart (length n) j.val =
        ⌊(n : ℝ) * (grid j : ℝ)⌋₊) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) (j : Fin (blocks + 1)) =>
        normalizedStepPath spatialScale n increments (grid j : ℝ))
      atTop
      (fun ω j => X (grid j) ω)
      (fun _ => iidSequenceLaw ν) P := by
  have hendpoints := tendstoInDistribution_endpoints_of_stableClock
    hDOA hX blocks grid hgrid hgridStart length spatialScale hblock hspatial
    hratio hcenter
  apply hendpoints.congr
  · intro n
    filter_upwards with increments
    funext j
    simp only [normalizedStepPath, hposition]
    rw [div_eq_mul_inv, mul_comm]
  · exact Filter.Eventually.of_forall fun _ => rfl

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
