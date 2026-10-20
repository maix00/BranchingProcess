/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.CyclicReindex
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Rotation.DriftedTube
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Rotation.FinitePath
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Rotation.LinearTube
public import Probability.Sequence.IID.FiniteReindex
public import Topology.Cadlag.Skorokhod.Path.Scaling

/-!
# Cyclic covers of finite path corridors

The public declarations are:

- `movingOffsetCorridorPath` and
  `offsetCorridorPath_removeLinearDrift_iff_moving`: subtracting $dj$ turns
  the cyclic moving corridor into the static offset corridor.
- `finiteCoordinateReindex_apply`, `IsCyclicPartialSumReindex`,
  `cyclicCoordinateReindex_isCyclicPartialSumReindex`, and
  `cyclicPartialSum_smul`: coordinate rotation, compatibility with partial
  sums, and scaling.
- `finiteLinearPathBall_knots_in_tube`: a $J_1$ ball of radius $r$ around
  slope $a$, with $|a|\le1$, gives
  $|S_j/\text{scale}-a(j/n)|<2r$ at every knot.
- `finiteLinearBall_subset_cyclicOffsetCover_allOffsets`,
  `finiteLinearBall_subset_cyclicOffsetCover_allOffsets_modular`, and
  `finiteLinearBall_subset_cyclicOffsetCover_allOffsets_of_normalizationRatio`:
  if $2r+|d|n<1/16$, the linear path ball is covered by the $n$ cyclic
  preimages of the drift-removed corridor for $u\in[0,1]$; the last theorem
  also allows different source and target spatial scales.
- `scalePath_finiteNormalizedStepPath_eq`: multiplying the source-normalized
  path by $\text{sourceScale}/\text{targetScale}$ gives the target-normalized
  path.
- `finiteLinearBall_subset_cyclicOffsetCover_lowerEdge` and
  `finiteLinearBall_subset_cyclicOffsetCover_lowerEdge_modular`: the centered
  path ball has the same cover for $u\in[0,1/10]$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Fin
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The moving corridor corresponding to a static offset corridor after
subtracting a per-step drift. Its endpoint band is translated by the total
drift `drift * n`; no zero-total-increment assumption is made. -/
def movingOffsetCorridorPath {n : ℕ} (drift u : ℝ)
    (s : Fin (n + 1) → ℝ) (k : Fin n) : Prop :=
  (∀ j, cyclicPartialSum s k j ∈
      Set.Icc (-u + drift * (j.val : ℝ))
        (1 - u + drift * (j.val : ℝ))) ∧
    cyclicPartialSum s k (Fin.last n) ∈
      Set.Icc (1 / 3 - u + drift * (n : ℝ))
        (2 / 3 - u + drift * (n : ℝ))

/-- Static survival for the drift-removed cyclic path is exactly survival in
the translated moving corridor for the original cyclic path. -/
theorem offsetCorridorPath_removeLinearDrift_iff_moving
    {n : ℕ} (drift u : ℝ) (s : Fin (n + 1) → ℝ) (k : Fin n) :
    offsetCorridorPath u (cyclicRotatePath (removeLinearDrift drift s) k) ↔
      movingOffsetCorridorPath drift u s k := by
  constructor
  · rintro ⟨hpath, hend⟩
    refine ⟨?_, ?_⟩
    · intro j
      have hj := hpath j
      change cyclicPartialSum (removeLinearDrift drift s) k j ∈
        Set.Icc (-u) (1 - u) at hj
      rw [cyclicPartialSum_removeLinearDrift s drift k j] at hj
      rcases hj with ⟨hlo, hhi⟩
      constructor <;> linarith
    · have hlast := hend
      change cyclicPartialSum (removeLinearDrift drift s) k (Fin.last n) ∈
        Set.Icc (1 / 3 - u) (2 / 3 - u) at hlast
      rw [cyclicPartialSum_removeLinearDrift s drift k (Fin.last n)] at hlast
      rw [Fin.val_last] at hlast
      rcases hlast with ⟨hlo, hhi⟩
      constructor <;> linarith
  · rintro ⟨hpath, hend⟩
    refine ⟨?_, ?_⟩
    · intro j
      have hj := hpath j
      change cyclicPartialSum s k j ∈
        Set.Icc (-u + drift * (j.val : ℝ))
          (1 - u + drift * (j.val : ℝ)) at hj
      change cyclicPartialSum (removeLinearDrift drift s) k j ∈
        Set.Icc (-u) (1 - u)
      rw [cyclicPartialSum_removeLinearDrift s drift k j]
      rcases hj with ⟨hlo, hhi⟩
      constructor <;> linarith
    · have hlast := hend
      change cyclicPartialSum s k (Fin.last n) ∈
        Set.Icc (1 / 3 - u + drift * (n : ℝ))
          (2 / 3 - u + drift * (n : ℝ)) at hlast
      change cyclicPartialSum (removeLinearDrift drift s) k (Fin.last n) ∈
        Set.Icc (1 / 3 - u) (2 / 3 - u)
      rw [cyclicPartialSum_removeLinearDrift s drift k (Fin.last n)]
      rw [Fin.val_last]
      rcases hlast with ⟨hlo, hhi⟩
      constructor <;> linarith

/-- Applying the finite-coordinate reindexing used by exchangeability
reorders the vector by the supplied equivalence. -/
@[simp]
theorem finiteCoordinateReindex_apply
    {n : ℕ} (e : Fin n ≃ Fin n) (x : Fin n → ℝ) (i : Fin n) :
    ProbabilityTheory.finiteCoordinateReindex e x i = x (e i) := by
  simpa [ProbabilityTheory.finiteCoordinateReindex,
    MeasurableEquiv.coe_piCongrLeft] using
    (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n => ℝ)
      e.symm x (e i))

/-- Compatibility condition between cyclic coordinate rotation and the
`n + 1` partial-sum knot path. This is stated separately so that the arithmetic
bridge can be reused independently of any probability law. -/
def IsCyclicPartialSumReindex {n : ℕ} (rotate : Fin n → Fin n ≃ Fin n) :
    Prop :=
  ∀ (x : Fin n → ℝ) (k : Fin n) (j : Fin (n + 1)),
    Fin.partialSum (fun i => x (rotate k i)) j =
      cyclicPartialSum (Fin.partialSum x) k j

/-- The generic cyclic-coordinate identity supplies the compatibility
condition used by the entrance estimate. -/
theorem cyclicCoordinateReindex_isCyclicPartialSumReindex {n : ℕ}
    (hn : 0 < n) :
    IsCyclicPartialSumReindex (fun k => cyclicCoordinateReindex hn k) := by
  intro x k j
  exact Fin.partialSum_cyclicCoordinateReindex hn x k j

/-- Scaling a finite partial-sum path commutes with taking a cyclic rotation. -/
theorem cyclicPartialSum_smul {n : ℕ} (s : Fin (n + 1) → ℝ)
    (c : ℝ) (k : Fin n) (j : Fin (n + 1)) :
    cyclicPartialSum (fun i => c * s i) k j =
      c * cyclicPartialSum s k j := by
  unfold cyclicPartialSum
  split_ifs <;> ring

/-- A path in the linear open ball has its finite knots in a linear tube. -/
theorem finiteLinearPathBall_knots_in_tube {n : ℕ} (hn : 0 < n)
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
theorem finiteLinearBall_subset_cyclicOffsetCover_allOffsets
    {n : ℕ} (hn : 0 < n) (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 1)
    (rotate : Fin n → Fin n ≃ Fin n)
    (hrotate : IsCyclicPartialSumReindex rotate) :
    finiteLinearPathBallEvent (n := n) scale (1 / 2 - u) radius ⊆
      ⋃ k, (ProbabilityTheory.finiteCoordinateReindex (rotate k)) ⁻¹'
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
  have hremove0 : removeLinearDrift drift s 0 = 0 := by
    simp [removeLinearDrift, hs0]
  let ε := 2 * radius + |drift| * (n : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε16 : ε < 1 / 16 := by simpa [ε] using hsmall
  have htube' : ∀ j,
      |removeLinearDrift drift s j - (1 / 2 - u) * normalizedTime j| < ε := by
    intro j
    have hbase := htube j
    have hjle : (j.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hdrift : |drift * (j.val : ℝ)| ≤ |drift| * (n : ℝ) := by
      have hjval : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_of_nonneg hjval]
      exact mul_le_mul_of_nonneg_left hjle (abs_nonneg _)
    have htriangle :
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
    rw [removeLinearDrift]
    dsimp [ε]
    linarith
  obtain ⟨k, hcorridor⟩ :=
    exists_offsetCorridorPath_of_linearTube_allOffsets hn hu
      (removeLinearDrift drift s) hremove0 hε16 htube'
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  change finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u
    (ProbabilityTheory.finiteCoordinateReindex (rotate k) x)
  change offsetCorridorPath u
    (removeLinearDrift drift
      (finiteNormalizedStepKnots scale
        (ProbabilityTheory.finiteCoordinateReindex (rotate k) x)))
  have hpath :
      removeLinearDrift drift
        (finiteNormalizedStepKnots scale
          (ProbabilityTheory.finiteCoordinateReindex (rotate k) x)) =
        cyclicRotatePath (removeLinearDrift drift s) k := by
    have hcoord : ProbabilityTheory.finiteCoordinateReindex (rotate k) x =
        fun i => x (rotate k i) := by
      funext i
      exact finiteCoordinateReindex_apply (rotate k) x i
    rw [hcoord]
    funext j
    change scale⁻¹ * Fin.partialSum (fun i => x (rotate k i)) j -
        drift * (j.val : ℝ) =
      cyclicPartialSum (removeLinearDrift drift s) k j
    calc
      scale⁻¹ * Fin.partialSum (fun i => x (rotate k i)) j -
          drift * (j.val : ℝ) =
        scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
          drift * (j.val : ℝ) := by rw [hrotate x k j]
      _ = cyclicPartialSum (removeLinearDrift drift s) k j := by
        rw [cyclicPartialSum_removeLinearDrift]
        change scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
            drift * (j.val : ℝ) =
          cyclicPartialSum (fun i => scale⁻¹ * Fin.partialSum x i) k j -
            drift * (j.val : ℝ)
        congr 1
        exact (cyclicPartialSum_smul (Fin.partialSum x) scale⁻¹ k j).symm
  rw [hpath]
  exact hcorridor

/-- The all-offset finite linear-ball cover for the concrete modular cyclic
rotations. -/
theorem finiteLinearBall_subset_cyclicOffsetCover_allOffsets_modular
    {n : ℕ} (hn : 0 < n) (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 1) :
    finiteLinearPathBallEvent (n := n) scale (1 / 2 - u) radius ⊆
      ⋃ k, (ProbabilityTheory.finiteCoordinateReindex
          (cyclicCoordinateReindex hn k)) ⁻¹'
        finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u := by
  exact finiteLinearBall_subset_cyclicOffsetCover_allOffsets
    hn scale drift radius u hradius hsmall hu
    (fun k => cyclicCoordinateReindex hn k)
    (cyclicCoordinateReindex_isCyclicPartialSumReindex hn)

/-- Changing the spatial normalization of a finite step path is exactly
pointwise spatial scaling. The ratio is `sourceScale / targetScale`: the
source path is divided by `sourceScale`, and multiplying it by this ratio
produces the path divided by `targetScale`. -/
theorem scalePath_finiteNormalizedStepPath_eq
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
theorem finiteLinearBall_subset_cyclicOffsetCover_allOffsets_of_normalizationRatio
    {n : ℕ} (hn : 0 < n) (targetScale sourceScale ratio drift sourceSlope
      radius u : ℝ)
    (htargetScale : targetScale ≠ 0) (hsourceScale : sourceScale ≠ 0)
    (hratio : ratio = sourceScale / targetScale)
    (hcenter : ratio * sourceSlope = 1 / 2 - u)
    (hradius : 0 < radius)
    (hsmall : 2 * (max 1 |ratio| * radius) +
      |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 1)
    (rotate : Fin n → Fin n ≃ Fin n)
    (hrotate : IsCyclicPartialSumReindex rotate) :
    finiteLinearPathBallEvent (n := n) sourceScale sourceSlope radius ⊆
      ⋃ k, (ProbabilityTheory.finiteCoordinateReindex (rotate k)) ⁻¹'
        finiteDriftRemovedOffsetCorridorEvent (n := n) targetScale drift u := by
  have htargetRadius : 0 < max 1 |ratio| * radius :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hradius
  have hcover := finiteLinearBall_subset_cyclicOffsetCover_allOffsets
    hn targetScale drift (max 1 |ratio| * radius) u htargetRadius hsmall hu
    rotate hrotate
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
theorem finiteLinearBall_subset_cyclicOffsetCover_lowerEdge
    {n : ℕ} (hn : 0 < n) (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 (1 / 10))
    (rotate : Fin n → Fin n ≃ Fin n)
    (hrotate : IsCyclicPartialSumReindex rotate) :
    finiteLinearPathBallEvent (n := n) scale (1 / 2) radius ⊆
      ⋃ k, (ProbabilityTheory.finiteCoordinateReindex (rotate k)) ⁻¹'
        finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u := by
  intro x hx
  have htube := finiteLinearPathBall_knots_in_tube hn scale (1 / 2) radius
    (by norm_num : |(1 / 2 : ℝ)| ≤ 1) hradius x hx
  let s : Fin (n + 1) → ℝ := finiteNormalizedStepKnots scale x
  have hs0 : s 0 = 0 := by simp [s, finiteNormalizedStepKnots]
  have hremove0 : removeLinearDrift drift s 0 = 0 := by
    simp [removeLinearDrift, hs0]
  let ε := 2 * radius + |drift| * (n : ℝ)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε16 : ε < 1 / 16 := by simpa [ε] using hsmall
  have htube : ∀ j,
      |removeLinearDrift drift s j - (1 / 2) * normalizedTime j| < ε := by
    intro j
    have hbase := htube j
    have hjle : (j.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ j.isLt
    have hdrift : |drift * (j.val : ℝ)| ≤ |drift| * (n : ℝ) := by
      have hjval : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
      rw [abs_mul, abs_of_nonneg hjval]
      exact mul_le_mul_of_nonneg_left hjle (abs_nonneg _)
    have htriangle :
        |(s j - drift * (j.val : ℝ)) - (1 / 2) * normalizedTime j| ≤
          |s j - (1 / 2) * normalizedTime j| + |drift * (j.val : ℝ)| := by
      calc
        |(s j - drift * (j.val : ℝ)) - (1 / 2) * normalizedTime j| =
            |(s j - (1 / 2) * normalizedTime j) - drift * (j.val : ℝ)| := by ring_nf
        _ ≤ |s j - (1 / 2) * normalizedTime j| +
            |drift * (j.val : ℝ)| := abs_sub _ _
    rw [removeLinearDrift]
    dsimp [ε]
    linarith
  have htube' : ∀ j,
      |removeLinearDrift drift s j - normalizedTime j / 2| < ε := by
    intro j
    simpa [div_eq_mul_inv, mul_comm] using htube j
  obtain ⟨k, hcorridor⟩ :=
    exists_offsetCorridorPath_of_linearTube_lowerEdge hn hu
      (removeLinearDrift drift s) hremove0 hε hε16 htube'
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  change finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u
    (ProbabilityTheory.finiteCoordinateReindex (rotate k) x)
  change offsetCorridorPath u
    (removeLinearDrift drift
      (finiteNormalizedStepKnots scale
        (ProbabilityTheory.finiteCoordinateReindex (rotate k) x)))
  have hpath :
      removeLinearDrift drift
        (finiteNormalizedStepKnots scale
        (ProbabilityTheory.finiteCoordinateReindex (rotate k) x)) =
        cyclicRotatePath (removeLinearDrift drift s) k := by
    have hcoord : ProbabilityTheory.finiteCoordinateReindex (rotate k) x =
        fun i => x (rotate k i) := by
      funext i
      exact finiteCoordinateReindex_apply (rotate k) x i
    rw [hcoord]
    funext j
    change scale⁻¹ * Fin.partialSum (fun i => x (rotate k i)) j -
        drift * (j.val : ℝ) =
      cyclicPartialSum (removeLinearDrift drift s) k j
    calc
      scale⁻¹ * Fin.partialSum (fun i => x (rotate k i)) j -
          drift * (j.val : ℝ) =
        scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
          drift * (j.val : ℝ) := by rw [hrotate x k j]
      _ = cyclicPartialSum (removeLinearDrift drift s) k j := by
        rw [cyclicPartialSum_removeLinearDrift]
        change scale⁻¹ * cyclicPartialSum (Fin.partialSum x) k j -
            drift * (j.val : ℝ) =
          cyclicPartialSum (fun i => scale⁻¹ * Fin.partialSum x i) k j -
            drift * (j.val : ℝ)
        congr 1
        exact (cyclicPartialSum_smul (Fin.partialSum x) scale⁻¹ k j).symm
  rw [hpath]
  exact hcorridor

/-- The linear-ball cover using the concrete modular cyclic rotations. -/
theorem finiteLinearBall_subset_cyclicOffsetCover_lowerEdge_modular
    {n : ℕ} (hn : 0 < n) (scale drift radius u : ℝ)
    (hradius : 0 < radius)
    (hsmall : 2 * radius + |drift| * (n : ℝ) < 1 / 16)
    (hu : u ∈ Set.Icc 0 (1 / 10)) :
    finiteLinearPathBallEvent (n := n) scale (1 / 2) radius ⊆
      ⋃ k, (ProbabilityTheory.finiteCoordinateReindex
          (cyclicCoordinateReindex hn k)) ⁻¹'
        finiteDriftRemovedOffsetCorridorEvent (n := n) scale drift u := by
  exact finiteLinearBall_subset_cyclicOffsetCover_lowerEdge
    hn scale drift radius u hradius hsmall hu
    (fun k => cyclicCoordinateReindex hn k)
    (cyclicCoordinateReindex_isCyclicPartialSumReindex hn)


end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
