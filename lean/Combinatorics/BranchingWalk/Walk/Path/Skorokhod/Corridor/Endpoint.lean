module

public import Combinatorics.BranchingWalk.Walk.Path.Skorokhod.Corridor
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Endpoint-constrained corridors for normalized walk paths

This file identifies an open Skorokhod corridor with an open endpoint
constraint with its finite random-walk path formulation.
-/

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- Closed Skorokhod corridor membership of the normalized step path is
equivalent to checking its positive grid values. -/
theorem normalizedStepCadlagPathIcc_mem_rangeInClosedInterval_iff_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lower upper : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper)
    (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInClosedInterval lower upper ↔
      InClosedCorridorOnGrid scale n (fun _ => lower) (fun _ => upper)
        increment := by
  constructor
  · intro h k
    let t : unitInterval :=
      ⟨((k.val + 1 : ℕ) : ℝ) / n, by
        constructor
        · positivity
        · rw [div_le_one (by positivity)]
          exact_mod_cast Nat.succ_le_iff.mpr k.isLt⟩
    have ht := (Skorokhod.mem_rangeInClosedInterval_iff.mp h) t
    change lower ≤ normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ∧
      normalizedStepPath scale n increment
        (((k.val + 1 : ℕ) : ℝ) / n) ≤ upper at ht
    dsimp only [InClosedCorridorOnGrid]
    rw [normalizedStepPath_grid scale hn] at ht ⊢
    exact ht
  · intro h
    have hlinear : normalizedLinearContinuousPathIcc scale n increment ∈
        ContinuousMap.rangeInClosedInterval lower upper :=
      (normalizedLinearContinuousPathIcc_mem_rangeInClosedInterval_iff
        scale hn hlower hupper increment).2 h
    have hlinear' := ContinuousMap.mem_rangeInClosedInterval_iff.mp hlinear
    intro t
    obtain ⟨s, hs⟩ :=
      exists_normalizedLinearContinuousPathIcc_eq_normalizedStepCadlagPathIcc
        scale hn increment t
    have hval := hlinear' s
    rw [← hs]
    exact hval

/-- Membership of the normalized step path in a centered open corridor with
an open terminal interval is exactly a strict finite tube together with the
corresponding normalized endpoint constraint. -/
theorem normalizedStepCadlagPathIcc_mem_centeredOpenIntervalEndsIn_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 < width)
    (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInOpenIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper ↔
      InOpenHorizontalTube (1 / 2) (width * scale n) n increment ∧
        partialSum n increment / scale n ∈
          Set.Ioo endpointLower endpointUpper := by
  rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff,
    normalizedStepCadlagPathIcc_mem_centeredOpenInterval_iff
      scale hn hscale hwidth]
  change _ ∧ normalizedStepPath scale n increment 1 ∈ _ ↔ _
  rw [normalizedStepPath_one, inv_mul_eq_div]

/-- A centered closed Skorokhod corridor of arbitrary nonnegative width is
the weak horizontal tube with that width in the original coordinates. -/
theorem normalizedStepCadlagPathIcc_mem_centeredClosedInterval_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width : ℝ} (hwidth : 0 ≤ width) (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2) ↔
      InHorizontalTube (1 / 2) (width * scale n) n increment := by
  rw [normalizedStepCadlagPathIcc_mem_rangeInClosedInterval_iff_grid
    scale hn (by linarith) (by linarith)]
  constructor
  · intro h k
    have hk := h k
    dsimp only [InClosedCorridorOnGrid] at hk
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div] at hk
    change -(1 / 2 : ℝ) * (width * scale n) ≤
        partialSum (k + 1) increment ∧
      partialSum (k + 1) increment ≤
        (1 - (1 / 2 : ℝ)) * (width * scale n)
    have hkl := (le_div_iff₀ hscale).mp hk.1
    have hku := (div_le_iff₀ hscale).mp hk.2
    constructor <;> nlinarith
  · intro h k
    dsimp only [InClosedCorridorOnGrid]
    rw [normalizedStepPath_grid scale hn, inv_mul_eq_div]
    have hk := h k
    change -(1 / 2 : ℝ) * (width * scale n) ≤
        partialSum (k + 1) increment ∧
      partialSum (k + 1) increment ≤
        (1 - (1 / 2 : ℝ)) * (width * scale n) at hk
    constructor
    · apply (le_div_iff₀ hscale).mpr
      nlinarith [hk.1]
    · apply (div_le_iff₀ hscale).mpr
      nlinarith [hk.2]

/-- Membership of the normalized step path in a centered closed corridor
with a closed terminal interval is exactly the weak finite tube together
with the normalized endpoint constraint. -/
theorem normalizedStepCadlagPathIcc_mem_centeredClosedIntervalEndsIn_iff
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (hscale : 0 < scale n)
    {width endpointLower endpointUpper : ℝ} (hwidth : 0 ≤ width)
    (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInClosedIntervalEndsIn
          (-(width / 2)) (width / 2) endpointLower endpointUpper ↔
      InHorizontalTube (1 / 2) (width * scale n) n increment ∧
        partialSum n increment / scale n ∈
          Set.Icc endpointLower endpointUpper := by
  rw [Skorokhod.mem_rangeInClosedIntervalEndsIn_iff,
    normalizedStepCadlagPathIcc_mem_centeredClosedInterval_iff
      scale hn hscale hwidth]
  change _ ∧ normalizedStepPath scale n increment 1 ∈ _ ↔ _
  rw [normalizedStepPath_one, inv_mul_eq_div]

end Combinatorics.Branching.Walk
