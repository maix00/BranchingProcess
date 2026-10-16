/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Gaussian.EscapeConstant
public import Probability.Process.Stable.SmallDeviation.PathClass.StepCorridor.Rate
public import Topology.Cadlag.Skorokhod.SmallDeviation.RangeCover

/-!
# Gaussian corridor cover of the range event

The public definitions in this file are
`ProbabilityTheory.RandomWalk.SmallDeviation.Range.rangeCoverLower`,
`rangeCoverUpper`, and `rangeCoverUnion`: the finite family of constant
corridors used to cover paths with bounded range.

The public theorems are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.rangeCoverLower_lt_zero`
  and `rangeCoverUpper_pos`: each selected corridor contains the origin.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.rangeCoverWidth`:
  each corridor has width $2(1+2/k)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.rangeCoverUnion_realEnergy`:
  the finite cover has the Gaussian corridor energy needed for the rate.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Range.rangeTubeStartingAtZero_subset_rangeCoverUnion`:
  the zero-starting bounded-range event is contained in this cover.

The non-strict range-oscillation event is covered by finitely many constant
corridors. The resulting Gaussian range estimate is a reusable consequence
of A. A. Mogul'skii, *Small Deviations in a Space of Trajectories*,
Theorem 3, Section 4, p. 764 of the 1974 Russian original (DOI 10.1137/1119081).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Range

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The lower and upper constant boundaries in the finite cover of a path
whose range diameter is less than two. -/
noncomputable def rangeCoverLower (k : ℕ) (j : Fin (2 * k + 1)) : ℝ :=
  (j.val : ℝ) / k - 1 - (1 + 2 / k)

noncomputable def rangeCoverUpper (k : ℕ) (j : Fin (2 * k + 1)) : ℝ :=
  (j.val : ℝ) / k - 1 + (1 + 2 / k)

theorem rangeCoverLower_lt_zero {k : ℕ} (hk : 0 < k)
    (j : Fin (2 * k + 1)) : rangeCoverLower k j < 0 := by
  have hj : (j.val : ℝ) ≤ 2 * k := by
    exact_mod_cast (Nat.lt_succ_iff.mp (by omega : j.val < 2 * k + 1))
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hj' : (j.val : ℝ) / k ≤ 2 :=
    (div_le_iff₀ hk').2 (by nlinarith [hj])
  have hterm : 0 < (2 : ℝ) / k := by positivity
  dsimp [rangeCoverLower]
  linarith

theorem rangeCoverUpper_pos {k : ℕ} (hk : 0 < k)
    (j : Fin (2 * k + 1)) : 0 < rangeCoverUpper k j := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  dsimp [rangeCoverUpper]
  have hj : 0 ≤ (j.val : ℝ) / k := div_nonneg (Nat.cast_nonneg _) hk'.le
  have hkPos : 0 < (2 : ℝ) / k := by positivity
  linarith

theorem rangeCoverWidth {k : ℕ} (j : Fin (2 * k + 1)) :
    rangeCoverUpper k j - rangeCoverLower k j = 2 * (1 + 2 / k) := by
  dsimp [rangeCoverUpper, rangeCoverLower]
  ring

/-- The finite M₃ union of constant corridors covering every zero-starting
path of range diameter less than two. -/
noncomputable def rangeCoverUnion (k : ℕ) (hk : 0 < k) :
    FiniteCorridorUnion 2 where
  count := 2 * k + 1
  count_pos := by omega
  pieces := fun j => ContinuousAdmissibleStepCorridor.constantBounds
    (rangeCoverLower_lt_zero hk j) (rangeCoverUpper_pos hk j)
  minimum_energy_pos := by
    have henergy (j : Fin (2 * k + 1)) :
        ContinuousAdmissibleStepCorridor.energy 2
          (ContinuousAdmissibleStepCorridor.constantBounds
            (rangeCoverLower_lt_zero hk j) (rangeCoverUpper_pos hk j)) =
          ENNReal.ofReal ((2 * (1 + 2 / (k : ℝ))) ^ (-2 : ℝ)) := by
      rw [ContinuousAdmissibleStepCorridor.energy_eq_widthCost_of_constant_values
        2 _ (rangeCoverUpper k j) (rangeCoverLower k j)]
      · have hwidth : 0 < rangeCoverUpper k j - rangeCoverLower k j := by
          rw [rangeCoverWidth]
          positivity
        rw [widthCost_coe_sub _ _ _ hwidth, rangeCoverWidth]
      · intro t
        simp [ContinuousAdmissibleStepCorridor.constantBounds,
          StepBoundary.eval_constant]
      · intro t
        simp [ContinuousAdmissibleStepCorridor.constantBounds,
          StepBoundary.eval_constant]
    have hpos : 0 < ENNReal.ofReal ((2 * (1 + 2 / (k : ℝ))) ^ (-2 : ℝ)) := by
      apply ENNReal.ofReal_pos.mpr
      exact Real.rpow_pos_of_pos (by positivity) _
    apply lt_of_lt_of_le hpos
    rw [finiteMinimumEnergy]
    apply (Finset.le_inf'_iff (s := Finset.univ)
      (H := Finset.univ_nonempty)
      (f := fun j : Fin (2 * k + 1) =>
        ContinuousAdmissibleStepCorridor.energy 2
          (ContinuousAdmissibleStepCorridor.constantBounds
            (rangeCoverLower_lt_zero hk j) (rangeCoverUpper_pos hk j)))).2
    intro j hj
    rw [henergy j]

theorem rangeCoverUnion_realEnergy (k : ℕ) (hk : 0 < k) :
    (rangeCoverUnion k hk).realEnergy =
      (2 * (1 + 2 / (k : ℝ))) ^ (-2 : ℝ) := by
  have henergyBase (j : Fin (2 * k + 1)) :
      ContinuousAdmissibleStepCorridor.energy 2
          (ContinuousAdmissibleStepCorridor.constantBounds
            (rangeCoverLower_lt_zero hk j) (rangeCoverUpper_pos hk j)) =
        ENNReal.ofReal ((2 * (1 + 2 / (k : ℝ))) ^ (-2 : ℝ)) := by
    rw [ContinuousAdmissibleStepCorridor.energy_eq_widthCost_of_constant_values
      2 _ (rangeCoverUpper k j) (rangeCoverLower k j)]
    · have hwidth : 0 < rangeCoverUpper k j - rangeCoverLower k j := by
        rw [rangeCoverWidth]
        positivity
      rw [widthCost_coe_sub _ _ _ hwidth, rangeCoverWidth]
    · intro t
      simp [ContinuousAdmissibleStepCorridor.constantBounds,
        StepBoundary.eval_constant]
    · intro t
      simp [ContinuousAdmissibleStepCorridor.constantBounds,
        StepBoundary.eval_constant]
  have henergy (j : Fin ((rangeCoverUnion k hk).count)) :
      ContinuousAdmissibleStepCorridor.energy 2
          ((rangeCoverUnion k hk).pieces j) =
        ENNReal.ofReal ((2 * (1 + 2 / (k : ℝ))) ^ (-2 : ℝ)) := by
    change ContinuousAdmissibleStepCorridor.energy 2
        (ContinuousAdmissibleStepCorridor.constantBounds
          (rangeCoverLower_lt_zero hk j) (rangeCoverUpper_pos hk j)) = _
    exact henergyBase j
  haveI : Nonempty (Fin ((rangeCoverUnion k hk).count)) :=
    Fin.pos_iff_nonempty.mp (rangeCoverUnion k hk).count_pos
  change (Finset.univ.inf' Finset.univ_nonempty
      (fun j : Fin ((rangeCoverUnion k hk).count) =>
        ContinuousAdmissibleStepCorridor.energy 2 ((rangeCoverUnion k hk).pieces j))).toReal = _
  have hmin := Finset.inf'_eq_of_forall (s := Finset.univ)
    (H := Finset.univ_nonempty)
    (f := fun j : Fin ((rangeCoverUnion k hk).count) =>
      ContinuousAdmissibleStepCorridor.energy 2 ((rangeCoverUnion k hk).pieces j))
    (a := ENNReal.ofReal ((2 * (1 + 2 / (k : ℝ))) ^ (-2 : ℝ)))
    (fun j hj => henergy j)
  rw [hmin]
  have hwidth : 0 < 2 * (1 + 2 / (k : ℝ)) := by positivity
  rw [ENNReal.toReal_ofReal (by positivity :
    0 ≤ (2 * (1 + 2 / (k : ℝ))) ^ (-2 : ℝ))]

/-- The finite cover from the range-tube lemma is exactly the corridor union
used by the M₃ rate theorem. -/
theorem rangeTubeStartingAtZero_subset_rangeCoverUnion
    (k : ℕ) (hk : 0 < k) :
    Skorokhod.rangeTubeStartingAtZero 1 ⊆ (rangeCoverUnion k hk).toSet := by
  intro path hpath
  have hcover := Skorokhod.rangeTubeStartingAtZero_subset_iUnion_corridors k hk hpath
  simp only [Set.mem_iUnion] at hcover
  rcases hcover with ⟨j, hj, hcorridor⟩
  have hj' : j < 2 * k + 1 := Finset.mem_range.mp hj
  have hstart : path ⊥ = 0 := hcorridor.1
  have hstrip : path ∈ Skorokhod.rangeInOpenInterval
      (((j : ℝ) / k - 1) - (1 + 2 / k))
      (((j : ℝ) / k - 1) + (1 + 2 / k)) := hcorridor.2
  rcases hstrip with ⟨margin, hmargin, hinside⟩
  let i : Fin ((rangeCoverUnion k hk).count) :=
    ⟨j, by simpa [rangeCoverUnion] using hj'⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  dsimp [rangeCoverUnion]
  rw [ContinuousAdmissibleStepCorridor.constantBounds_toSet]
  constructor
  · exact hstart
  · intro t
    constructor
    · have h := (hinside t).1
      dsimp [rangeCoverLower]
      linarith
    · have h := (hinside t).2
      dsimp [rangeCoverUpper]
      linarith

end ProbabilityTheory.RandomWalk.SmallDeviation.Range

end
