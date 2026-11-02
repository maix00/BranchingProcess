/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Algebra.BigOperators.CyclicReindex
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.FinitePath
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.LinearTube
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.Lemmas.Rotation.OffsetCorridorEvent
import all Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomainEvent
import Topology.Cadlag.Skorokhod.Path.Scaling

/-!
# Cyclic covers of finite path corridors

## Internal proof declarations

- `finiteLinearBall_subset_cyclicOffsetCover_allOffsets` and
  `finiteLinearBall_subset_cyclicOffsetCover_allOffsets_of_normalizationRatio`:
  if $2r+|d|n<1/16$, the linear path ball is covered by the $n$ cyclic
  preimages of the drift-removed corridor for $u\in[0,1]$; the last theorem
  also allows different source and target spatial scales.
- `finiteLinearBall_subset_cyclicOffsetCover_lowerEdge`: the centered path
  ball has the same cover for $u\in[0,1/10]$.

In each result, every path in the indicated linear-path ball belongs to at
least one cyclic preimage of the stated drift-removed corridor.

The finite corridor cover is a proof step in Wang Yiyang, *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (master's thesis,
Fudan University, 2026), Appendix A.2, Lemma A.7, used in the proof of
Chapter 3, Lemma 3.5. The reusable cyclic reindexing identities are imported
from `Algebra.BigOperators.CyclicReindex`.
-/

section

open MeasureTheory ProbabilityTheory Fin
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- Scaling a finite partial-sum path commutes with taking a cyclic rotation. -/
private lemma cyclicPartialSum_smul {n : ℕ} (s : Fin (n + 1) → ℝ)
    (c : ℝ) (k : Fin n) (j : Fin (n + 1)) :
    cyclicPartialSum (fun i => c * s i) k j =
      c * cyclicPartialSum s k j := by
  unfold cyclicPartialSum
  split_ifs <;> ring

/-- A path in the linear open ball has its finite knots in a linear tube. -/
private lemma finiteLinearPathBall_knots_in_tube {n : ℕ} (hn : 0 < n)
    (scale slope radius : ℝ) (hslopesmall : |slope| ≤ 1)
    (hradius : 0 < radius)
    (x : Fin n → ℝ)
    (hx : x ∈ finiteLinearPathBallEvent (n := n) scale slope radius) :
    ∀ j : Fin (n + 1),
      |finiteNormalizedStepKnots scale x j -
        slope * normalizedTime j| < 2 * radius := by
  have hdist : dist (finiteNormalizedStepPath scale x)
      (Skorokhod.linearPath slope) < radius := by
    simpa [finiteLinearPathBallEvent, Metric.mem_ball] using hx
  have htube := Skorokhod.abs_sub_linear_lt_two_mul_of_dist_lt
    hradius hslopesmall hdist
  intro j
  have hj := htube (normalizedGridPoint hn j)
  rw [finiteNormalizedStepPath_apply_grid hn scale x j] at hj
  simpa [normalizedGridPoint, normalizedTime, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hj

/-- A finite path in a narrow `J₁` ball around the offset-dependent line has
a cyclic reindexing whose drift-removed knots lie in the static offset
corridor. The deterministic rotation works for every fixed `u ∈ [0,1]`;
the finite-product probability estimate below then loses a factor `n`. -/
lemma finiteLinearBall_subset_cyclicOffsetCover_allOffsets
    {n : ℕ} (hn : 0 < n) (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 1) :
    finiteLinearPathBallEvent (n := n) scale (1 / 2 - u) radius ⊆
      ⋃ k, (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
          (finCycle k).symm) ⁻¹'
        finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u := by
  intro x hx
  have hslopesmall : |(1 / 2 - u)| ≤ 1 := by
    rw [abs_le]
    rcases hu with ⟨hu0, hu1⟩
    constructor <;> linarith
  have htube := finiteLinearPathBall_knots_in_tube hn scale (1 / 2 - u)
    radius hslopesmall hradius x hx
  let s : Fin (n + 1) → ℝ := finiteNormalizedStepKnots scale x
  have hs0 : s 0 = 0 := by simp [s, finiteNormalizedStepKnots]
  have hremove0 : Fin.removeLinearDrift drift s 0 = 0 := by
    simp [Fin.removeLinearDrift, hs0]
  let ε := 2 * radius + |drift| * (n : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε16 : ε < 1 / 16 := by simpa [ε] using hsmall
  have htube' : ∀ j,
      |Fin.removeLinearDrift drift s j - (1 / 2 - u) * normalizedTime j| < ε := by
    intro j
    have hbase := htube j
    have hjle : (j.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hdrift : |drift * (j.val : ℝ)| ≤ |drift| * (n : ℝ) := by
      have hjval : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_of_nonneg hjval]
      exact mul_le_mul_of_nonneg_left hjle (abs_nonneg _)
    have htriangleReal :
        |(s j - drift * (j.val : ℝ)) - (1 / 2 - u) * normalizedTime j| ≤
          |s j - (1 / 2 - u) * normalizedTime j| +
            |drift * (j.val : ℝ)| := by
      calc
        |(s j - drift * (j.val : ℝ)) -
            (1 / 2 - u) * normalizedTime j| =
            |(s j - (1 / 2 - u) * normalizedTime j) -
              drift * (j.val : ℝ)| := by ring_nf
        _ ≤ |s j - (1 / 2 - u) * normalizedTime j| +
            |drift * (j.val : ℝ)| := abs_sub _ _
    have htriangle :
        |Fin.removeLinearDrift drift s j -
          (1 / 2 - u) * normalizedTime j| ≤
          |s j - (1 / 2 - u) * normalizedTime j| +
            |drift * (j.val : ℝ)| := by
      simpa [Fin.removeLinearDrift, nsmul_eq_mul, mul_comm] using htriangleReal
    dsimp [Fin.removeLinearDrift] at htriangle
    rw [Fin.removeLinearDrift]
    dsimp [ε]
    linarith
  obtain ⟨k, hcorridor⟩ :=
    exists_offsetCorridorPath_of_linearTube_allOffsets hn hu
      (Fin.removeLinearDrift drift s) hremove0 hε16 htube'
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  change finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
      (finCycle k).symm x)
  change offsetCorridorPath u
    (Fin.removeLinearDrift drift
      (finiteNormalizedStepKnots scale
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
          (finCycle k).symm x)))
  have hpath :
      Fin.removeLinearDrift drift
        (finiteNormalizedStepKnots scale
          (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
            (finCycle k).symm x)) =
        cyclicRotatePath (Fin.removeLinearDrift drift s) k := by
    have hcoord : MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
        (finCycle k).symm x =
        fun i => x (finCycle k i) := by
      funext i
      have hcancel : (finCycle k).symm (finCycle k i) = i :=
        Equiv.symm_apply_apply _ _
      have h := Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => ℝ)
        (finCycle k).symm x (finCycle k i)
      rw [hcancel] at h
      simpa [MeasurableEquiv.coe_piCongrLeft] using h
    rw [hcoord]
    funext j
    change Fin.removeLinearDrift drift
        (finiteNormalizedStepKnots scale
          (fun i => x (finCycle k i))) j =
      cyclicPartialSum (Fin.removeLinearDrift drift s) k j
    calc
      Fin.removeLinearDrift drift
          (finiteNormalizedStepKnots scale
            (fun i => x (finCycle k i))) j =
        scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
          j.val • drift := by
            simp only [Fin.removeLinearDrift, finiteNormalizedStepKnots]
            rw [Fin.partialSum_finCycle x k j]
      _ = cyclicPartialSum (Fin.removeLinearDrift drift s) k j := by
        rw [Fin.cyclicPartialSum_removeLinearDrift]
        change scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
            j.val • drift =
          cyclicPartialSum (fun i => scale⁻¹ * Fin.partialSum x i) k j -
            j.val • drift
        congr 1
        exact (cyclicPartialSum_smul (Fin.partialSum x) scale⁻¹ k j).symm
  rw [hpath]
  exact hcorridor

/-- Changing the spatial normalization of a finite step path is exactly
pointwise spatial scaling. The ratio is `sourceScale / targetScale`: the
source path is divided by `sourceScale`, and multiplying it by this ratio
produces the path divided by `targetScale`. -/
private lemma scalePath_finiteNormalizedStepPath_eq
    {n : ℕ} (targetScale sourceScale ratio : ℝ)
    (htarget : targetScale ≠ 0) (hsource : sourceScale ≠ 0)
    (hratio : ratio = sourceScale / targetScale)
    (x : Fin n → ℝ) :
    Skorokhod.scalePath ratio (finiteNormalizedStepPath sourceScale x) =
      finiteNormalizedStepPath targetScale x := by
  have hnorm : ratio * sourceScale⁻¹ = targetScale⁻¹ := by
    rw [hratio, div_eq_mul_inv]
    field_simp [htarget, hsource]
  ext t
  simp only [Skorokhod.scalePath_apply, finiteNormalizedStepPath,
    RandomWalk.normalizedStepCadlagPathIcc_apply,
    RandomWalk.normalizedStepPath]
  rw [← hnorm]
  ring

/-- A linear ball at the source normalization is mapped into a linear ball at
the target normalization. This is the finite-path adapter for the generic
J₁ spatial-scaling estimate. -/
lemma finiteLinearBall_subset_cyclicOffsetCover_allOffsets_of_normalizationRatio
    {n : ℕ} (hn : 0 < n) (targetScale sourceScale ratio drift sourceSlope
      radius u : ℝ)
    (htargetScale : targetScale ≠ 0) (hsourceScale : sourceScale ≠ 0)
    (hratio : ratio = sourceScale / targetScale)
    (hcenter : ratio * sourceSlope = 1 / 2 - u)
    (hradius : 0 < radius)
    (hsmall : 2 * (max 1 |ratio| * radius) +
      |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 1) :
    finiteLinearPathBallEvent (n := n) sourceScale sourceSlope radius ⊆
      ⋃ k, (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
          (finCycle k).symm) ⁻¹'
        finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u := by
  have htargetRadius : 0 < max 1 |ratio| * radius :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hradius
  have hcover := finiteLinearBall_subset_cyclicOffsetCover_allOffsets
    hn targetScale drift (max 1 |ratio| * radius) u htargetRadius hsmall hu
  intro x hx
  have hsource : finiteNormalizedStepPath sourceScale x ∈
      Metric.ball (Skorokhod.linearPath sourceSlope) radius := hx
  have htarget : finiteNormalizedStepPath targetScale x ∈
      Metric.ball (Skorokhod.linearPath (1 / 2 - u))
        (max 1 |ratio| * radius) := by
    rw [Metric.mem_ball] at hsource ⊢
    rw [← scalePath_finiteNormalizedStepPath_eq targetScale sourceScale ratio
      htargetScale hsourceScale hratio x]
    have hscaled := Skorokhod.dist_scalePath_linearPath_lt
      (scale := ratio) (slope := sourceSlope) hsource
    simpa [hcenter] using hscaled
  exact hcover htarget

/-- Any finite path in a sufficiently narrow linear `J₁` ball has a cyclic
reindexing whose drift-removed knots lie in the static offset corridor. The
drift allowance is explicit: its total displacement over `n` steps is bounded
by `|drift| * n`. -/
lemma finiteLinearBall_subset_cyclicOffsetCover_lowerEdge
    {n : ℕ} (hn : 0 < n) (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 (1 / 10)) :
    finiteLinearPathBallEvent (n := n) scale (1 / 2) radius ⊆
      ⋃ k, (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
          (finCycle k).symm) ⁻¹'
        finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u := by
  intro x hx
  have htube := finiteLinearPathBall_knots_in_tube hn scale (1 / 2) radius
    (by norm_num : |(1 / 2 : ℝ)| ≤ 1) hradius x hx
  let s : Fin (n + 1) → ℝ := finiteNormalizedStepKnots scale x
  have hs0 : s 0 = 0 := by simp [s, finiteNormalizedStepKnots]
  have hremove0 : Fin.removeLinearDrift drift s 0 = 0 := by
    simp [Fin.removeLinearDrift, hs0]
  let ε := 2 * radius + |drift| * (n : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε16 : ε < 1 / 16 := by simpa [ε] using hsmall
  have htube : ∀ j,
      |Fin.removeLinearDrift drift s j - (1 / 2) * normalizedTime j| < ε := by
    intro j
    have hbase := htube j
    have hjle : (j.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hdrift : |drift * (j.val : ℝ)| ≤ |drift| * (n : ℝ) := by
      have hjval : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_of_nonneg hjval]
      exact mul_le_mul_of_nonneg_left hjle (abs_nonneg _)
    have htriangleReal :
        |(s j - drift * (j.val : ℝ)) - (1 / 2) * normalizedTime j| ≤
          |s j - (1 / 2) * normalizedTime j| + |drift * (j.val : ℝ)| := by
      calc
        |(s j - drift * (j.val : ℝ)) - (1 / 2) * normalizedTime j| =
            |(s j - (1 / 2) * normalizedTime j) - drift * (j.val : ℝ)| := by ring_nf
        _ ≤ |s j - (1 / 2) * normalizedTime j| +
            |drift * (j.val : ℝ)| := abs_sub _ _
    have htriangle :
        |Fin.removeLinearDrift drift s j -
          (1 / 2) * normalizedTime j| ≤
          |s j - (1 / 2) * normalizedTime j| +
            |drift * (j.val : ℝ)| := by
      simpa [Fin.removeLinearDrift, nsmul_eq_mul, mul_comm] using htriangleReal
    dsimp [Fin.removeLinearDrift] at htriangle
    rw [Fin.removeLinearDrift]
    dsimp [ε]
    linarith
  have htube' : ∀ j,
      |Fin.removeLinearDrift drift s j - normalizedTime j / 2| < ε := by
    intro j
    simpa [div_eq_mul_inv, mul_comm] using htube j
  obtain ⟨k, hcorridor⟩ :=
    exists_offsetCorridorPath_of_linearTube_lowerEdge hn hu
      (Fin.removeLinearDrift drift s) hremove0 hε hε16 htube'
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  change finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
      (finCycle k).symm x)
  change offsetCorridorPath u
    (Fin.removeLinearDrift drift
      (finiteNormalizedStepKnots scale
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
          (finCycle k).symm x)))
  have hpath :
      Fin.removeLinearDrift drift
        (finiteNormalizedStepKnots scale
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
          (finCycle k).symm x)) =
        cyclicRotatePath (Fin.removeLinearDrift drift s) k := by
    have hcoord : MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ)
        (finCycle k).symm x =
        fun i => x (finCycle k i) := by
      funext i
      have hcancel : (finCycle k).symm (finCycle k i) = i :=
        Equiv.symm_apply_apply _ _
      have h := Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => ℝ)
        (finCycle k).symm x (finCycle k i)
      rw [hcancel] at h
      simpa [MeasurableEquiv.coe_piCongrLeft] using h
    rw [hcoord]
    funext j
    change Fin.removeLinearDrift drift
        (finiteNormalizedStepKnots scale
          (fun i => x (finCycle k i))) j =
      cyclicPartialSum (Fin.removeLinearDrift drift s) k j
    calc
      Fin.removeLinearDrift drift
          (finiteNormalizedStepKnots scale
            (fun i => x (finCycle k i))) j =
        scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
          j.val • drift := by
            simp only [Fin.removeLinearDrift, finiteNormalizedStepKnots]
            rw [Fin.partialSum_finCycle x k j]
      _ = cyclicPartialSum (Fin.removeLinearDrift drift s) k j := by
        rw [Fin.cyclicPartialSum_removeLinearDrift]
        change scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
            j.val • drift =
          cyclicPartialSum (fun i => scale⁻¹ * Fin.partialSum x i) k j -
            j.val • drift
        congr 1
        exact (cyclicPartialSum_smul (Fin.partialSum x) scale⁻¹ k j).symm
  rw [hpath]
  exact hcorridor


end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
