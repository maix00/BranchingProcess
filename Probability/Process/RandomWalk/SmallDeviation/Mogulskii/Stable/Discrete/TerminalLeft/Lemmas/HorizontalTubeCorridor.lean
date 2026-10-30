/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.ContinuousBoundary
/-!
# Terminal-left corridor proof lemmas for horizontal tubes

## Internal proof declarations

- `sourceRelativeConstantCorridorEvent scale n lower upper` denotes the event
  that the terminal-left normalized path lies in the strict constant corridor
  $(\text{lower},\text{upper})$.
- `sourceRelativeConstantCorridor_subset_horizontalTube` proves that a
  corridor strictly inside $(-a,1-a)$ implies membership in the closed
  horizontal tube.
- `horizontalTube_subset_sourceRelativeConstantCorridor` proves that the
  closed horizontal tube lies in every strictly wider source corridor.

These deterministic event comparisons support the closed-tube rate transfer
in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 3, Lemma 3.1(i).
The terminal-left rate input is A. A. Mogul'skii, Theorem 3, Section 4,
p. 764, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; its English
translation is “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The terminal-left normalized walk path lies in the strict corridor
between the two constant boundaries. This is the terminal-left path event used in
the finite-variance closed-tube and endpoint-window rate transfers. -/
def sourceRelativeConstantCorridorEvent (scale : ℕ → ℝ) (n : ℕ)
    (lower upper : ℝ) : Set (ℕ → ℝ) :=
  {increment | terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
    relativeContinuousBoundaryCorridorSet
      (ContinuousMap.const unitInterval lower) (ContinuousMap.const unitInterval upper)}


private lemma normalizedSourcePartialSum_bounds_of_horizontalTube
    {n : ℕ} {scale : ℕ → ℝ} {a : ℝ} {increment : ℕ → ℝ}
    (hscale : 0 < scale n) (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1)
    (htube : InHorizontalTube a (scale n) (n - 1) increment)
    (k : Fin n) :
    -a ≤ (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∧
      (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ≤ 1 - a := by
  by_cases hk : k.val = 0
  · simp [hk, AdditivePath.displacement_zero]
    exact ⟨by linarith, by linarith⟩
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    let i : Fin (n - 1) := ⟨k.val - 1, by omega⟩
    have hi := htube i
    have hindex : i.val + 1 = k.val := by simp [i]; omega
    have hlow : -a ≤ AdditivePath.displacement (k : ℕ) increment / scale n := by
      apply (le_div_iff₀ hscale).2
      simpa [hindex] using hi.1
    have hhigh : AdditivePath.displacement (k : ℕ) increment / scale n ≤ 1 - a := by
      apply (div_le_iff₀ hscale).2
      simpa [hindex] using hi.2
    have hdiv : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment =
        AdditivePath.displacement (k : ℕ) increment / scale n := by
      rw [div_eq_mul_inv]
      ring
    rw [hdiv]
    exact ⟨hlow, hhigh⟩

/-- A strict constant source corridor whose boundaries lie inside a closed
horizontal tube forces the source walk to stay in that tube. -/
lemma sourceRelativeConstantCorridor_subset_horizontalTube
    {n : ℕ} {scale : ℕ → ℝ} {a lower upper : ℝ}
    (hn : 0 < n) (hscale : 0 < scale n)
    (hlower : -a < lower) (hupper : upper < 1 - a) :
    sourceRelativeConstantCorridorEvent scale n lower upper ⊆
      {increment | InHorizontalTube a (scale n) (n - 1) increment} := by
  intro increment hcorridor
  change terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.terminalLeftPathSpace ∧
    terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
      continuousBoundaryCorridorSet (ContinuousMap.const unitInterval lower) (ContinuousMap.const unitInterval upper)
    at hcorridor
  rcases hcorridor.2 with ⟨_, hbetween⟩
  have hrange := terminalLeftNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    scale hn increment
  intro i
  let k : Fin n := ⟨i.val + 1, by omega⟩
  have hvalue : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∈
      Set.range (terminalLeftNormalizedStepCadlagPathIcc scale n increment) := by
    have hfinite : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∈
        Set.range (fun j : Fin n =>
          (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment) :=
      ⟨k, rfl⟩
    exact hrange.symm ▸ hfinite
  obtain ⟨t, ht⟩ := hvalue
  have hbounds := hbetween t
  rw [ht, ContinuousMap.const_apply] at hbounds
  have hlow : -a ≤ (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment :=
    le_of_lt (lt_trans hlower hbounds.1)
  have hhigh : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ≤ 1 - a :=
    le_of_lt (lt_trans hbounds.2 hupper)
  have hlow' : -a * scale n ≤ AdditivePath.displacement (k : ℕ) increment := by
    apply (le_div_iff₀ hscale).1
    simpa [div_eq_mul_inv, mul_comm] using hlow
  have hhigh' : AdditivePath.displacement (k : ℕ) increment ≤
      (1 - a) * scale n := by
    apply (div_le_iff₀ hscale).1
    simpa [div_eq_mul_inv, mul_comm] using hhigh
  simpa [InHorizontalTube, k] using And.intro hlow' hhigh'

/-- A closed horizontal tube lies inside any strictly wider constant source
corridor, including the terminal-left path's terminal-left endpoint. -/
lemma horizontalTube_subset_sourceRelativeConstantCorridor
    {n : ℕ} {scale : ℕ → ℝ} {a lower upper : ℝ}
    (hn : 0 < n) (hscale : 0 < scale n) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hlower : lower < -a) (hupper : 1 - a < upper) :
    {increment | InHorizontalTube a (scale n) (n - 1) increment} ⊆
      sourceRelativeConstantCorridorEvent scale n lower upper := by
  intro increment htube
  let path := terminalLeftNormalizedStepCadlagPathIcc scale n increment
  have hzero : path ⊥ = 0 := by
    have hbot : (⊥ : unitInterval) ≠ ⊤ := by norm_num [unitInterval]
    rw [show path = terminalLeftNormalizedStepCadlagPathIcc scale n increment by rfl,
      terminalLeftNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment hbot]
    simp [normalizedStepPath, AdditivePath.displacement_zero]
  have hrange := terminalLeftNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    scale hn increment
  have hnormalized (k : Fin n) :
      -a ≤ (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∧
        (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ≤ 1 - a :=
    normalizedSourcePartialSum_bounds_of_horizontalTube hscale ha0 ha1 htube k
  refine ⟨Skorokhod.terminalLeftPath_mem_space
    (normalizedStepCadlagPathIcc scale n increment), ?_⟩
  change path ⊥ = 0 ∧ ∀ t : unitInterval,
    lower < path t ∧ path t < upper
  refine ⟨hzero, ?_⟩
  intro t
  have hvalue : path t ∈ Set.range path := ⟨t, rfl⟩
  rw [hrange] at hvalue
  obtain ⟨k, hk⟩ := hvalue
  have hbounds := hnormalized k
  have hboundsPath : -a ≤ path t ∧ path t ≤ 1 - a := by
    simpa only [← hk] using hbounds
  exact ⟨lt_of_lt_of_le hlower hboundsPath.1,
    lt_of_le_of_lt hboundsPath.2 hupper⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
