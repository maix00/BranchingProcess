/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.PathCount
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.ExitTime
public import Probability.Process.RandomWalk.Path.Corridor.Affine

/-!
# Expected cumulative population in a horizontal corridor

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_cumulativePopulation_le_meanExitTime`:
  for a boundary-normalized branching random walk starting at zero, the
  expected number of positive-generation particles with ancestral paths in
  $[-w,0]$ is at most the tilted walk's mean exit time $\mathbb E_\nu[\tau_w]$.

-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk

private lemma prefix_mem_iff_inHorizontalTube (width : ℝ) (hw : 0 ≤ width)
    (n : ℕ) (z : ℕ → ℝ) :
    history n 0 z ∈ affineCorridorPrefix n (-width) 0 width ↔
      InHorizontalTube 1 width n z := by
  constructor
  · intro h j
    have hj := h j.succ
    simpa [history_apply] using hj
  · intro h j
    by_cases hj : j.val = 0
    · have heq : j = 0 := Fin.ext hj
      subst j
      simpa using hw
    · have hstep := h ⟨j.val - 1, by omega⟩
      have heq : j.val - 1 + 1 = j.val := by omega
      simpa [history_apply, heq] using hstep

/-- The many-to-one and tail-sum comparison in Wang Yiyang, *Asymptotic
Speed of the N-Branching Random Walk with Infinite Offspring* (Fudan
University, 2026), Chapter 3, Lemma 3.8, proof of equation (3.11). -/
theorem lintegral_cumulativePopulation_le_meanExitTime
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {width : ℝ} (hw : 0 ≤ width) :
    (∫⁻ ω, ∑' n : ℕ, pathGeneration φ (n + 1)
      ((affineCorridorPrefix (n + 1) (-width) 0 width).indicator
        (fun _ => (1 : ℝ≥0∞))) 0 ω ∂offspringFieldLaw μ) ≤
      ∫⁻ z, (upperBoundaryExitTime width z : ℝ≥0∞) ∂tiltedIncrementFieldLaw φ μ := by
  let count (n : ℕ) : StepField ℕ X → ℝ≥0∞ := pathGeneration φ (n + 1)
    ((affineCorridorPrefix (n + 1) (-width) 0 width).indicator
      (fun _ => (1 : ℝ≥0∞))) 0
  have hcount (n : ℕ) : Measurable (count n) :=
    pathGeneration_measurable φ (n + 1)
      (measurable_const.indicator (measurableSet_affineCorridorPrefix ..)) 0
  change (∫⁻ ω, ∑' n, count n ω ∂offspringFieldLaw μ) ≤ _
  rw [lintegral_tsum (fun n => (hcount n).aemeasurable), lintegral_upperBoundaryExitTime_eq_tsum]
  let P := tiltedIncrementFieldLaw φ μ
  calc
    _ ≤ ∑' n : ℕ, horizontalTubeProbability P 1 width (n + 1) := by
      apply tsum_le_tsum
      intro n
      have h := lintegral_pathGeneration_le_exp_mul_spineProbability φ μ hboundary
        (n + 1) 0 0 (affineCorridorPrefix (n + 1) (-width) 0 width)
        (measurableSet_affineCorridorPrefix ..) (fun _ hp => by
          simpa using (hp ⟨n + 1, Nat.lt_succ_self _⟩).2)
      have hevent : {z | history (n + 1) 0 z ∈ affineCorridorPrefix (n + 1) (-width) 0 width} =
          {z | InHorizontalTube 1 width (n + 1) z} :=
        Set.ext (prefix_mem_iff_inHorizontalTube width hw (n + 1))
      simpa only [count, P, horizontalTubeProbability, hevent, sub_self, Real.exp_zero,
        ENNReal.ofReal_one, one_mul] using h
    _ ≤ ∑' n : ℕ, horizontalTubeProbability P 1 width n := by
      calc
        _ ≤ horizontalTubeProbability P 1 width 0 +
              ∑' n : ℕ, horizontalTubeProbability P 1 width (n + 1) :=
          le_add_of_nonneg_left zero_le
        _ = _ := (tsum_eq_zero_add' (f := fun n => horizontalTubeProbability P 1 width n)
          CompleteLattice.summable).symm

end ProbabilityTheory.BranchingRandomWalk.Spine

end
