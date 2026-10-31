/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.WalkGrid
import Probability.Process.Stable.PathLaw.Basic
import Probability.ConvergenceInDistribution.CadlagPath.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Proof support for monotone stable position-grid laws

For an edge index `i : Fin (n + 1)`, the coordinate maps insert a zero
increment into `Fin n → ℝ` and repeat the corresponding position in
`Fin (n + 1) → ℝ`. If the `i`th factor is `Measure.dirac 0` and the other
factors agree under `i.succAbove`, their product measure is the pushforward
of the shorter product measure by zero-coordinate insertion. These identities
and the zero-start argument support
`ProbabilityTheory.stableGridPositionLaws_of_strictGridPositionLaws`; the
finite tuple operations are built from Mathlib's `Fin.insertNth` and
`MeasurableEquiv.piFinSuccAbove` APIs.

## Internal proof declarations

The declarations below are in
`ProbabilityTheory.StablePathLaw.MonotoneGrid.Lemmas`.

- `insertZeroCoordinate`, `measurable_insertZeroCoordinate`,
  `contractNth_insertZeroCoordinate`, and `partialSum_insertZeroCoordinate`
  define insertion of a zero increment, prove measurability and recovery by
  `Fin.contractNth`, and give
  `Fin.partialSum (insertZeroCoordinate i x) =
  insertRepeatedPosition i (Fin.partialSum x)`.
- `insertRepeatedPosition`, `removeRepeatedPosition`,
  `measurable_insertRepeatedPosition`, and
  `measurable_removeRepeatedPosition` define measurable insertion and deletion
  of an adjacent repeated coordinate. The identity
  `removeRepeatedPosition_insertRepeatedPosition` states that
  `removeRepeatedPosition i (insertRepeatedPosition i x) = x` always holds;
  `insertRepeatedPosition_removeRepeatedPosition_of_diagonal` gives the
  reverse identity when the adjacent coordinates agree.
  `map_removeRepeatedPosition_insertRepeatedPosition` and
  `map_insertRepeatedPosition_removeRepeatedPosition_of_ae_diagonal` give the
  associated pushforward identities, including the reverse identity under an
  almost-everywhere diagonal hypothesis.
- `deleteRepeatedPointGrid`, `deleteRepeatedPointGrid_monotone`,
  `deleteRepeatedPointGrid_start`,
  `deleteRepeatedPointGrid_increment_interval`, and
  `denseEvaluation_insertRepeatedPoint` delete one repeated grid point while
  preserving the initial point and monotonicity, and identify the resulting
  path evaluations and increment intervals.
- `measure_pi_insertZeroCoordinate` states that replacing the inserted factor
  by `Measure.dirac 0` and matching all other factors under `Fin.succAbove`
  gives
  `Measure.pi ν = (Measure.pi μ).map (insertZeroCoordinate i)`.
- `ae_start_eq_zero_of_strictGridPositionLaws` states that the strict-grid
  position-law identities imply $f(0)=0$ almost surely.
-/

section

open MeasureTheory
open MeasureTheory.CadlagPath
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

namespace ProbabilityTheory.StablePathLaw.MonotoneGrid.Lemmas

/-- Insert a zero coordinate at `i`, shifting the remaining coordinates by
`Fin.succAbove`. -/
def insertZeroCoordinate {n : ℕ} (i : Fin (n + 1))
    (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.insertNth i 0 x

lemma measurable_insertZeroCoordinate {n : ℕ} (i : Fin (n + 1)) :
    Measurable (@insertZeroCoordinate n i) := by
  change Measurable
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm ∘
      fun x : Fin n → ℝ => (0, x))
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm.measurable.comp
    (measurable_const.prodMk measurable_id)

/-- Insert a repeated position at the endpoint immediately after edge `i`. -/
def insertRepeatedPosition {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ :=
  Fin.insertNth i.succ (x i) x

/-- Restrict a position vector to the coordinates remaining after deleting
the repeated endpoint. -/
def removeRepeatedPosition {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => x ((i.succ).succAbove j)

lemma measurable_removeRepeatedPosition {n : ℕ} (i : Fin (n + 1)) :
    Measurable (@removeRepeatedPosition n i) := by
  rw [measurable_pi_iff]
  intro j
  exact measurable_pi_apply ((i.succ).succAbove j)

@[simp]
lemma removeRepeatedPosition_insertRepeatedPosition {n : ℕ} (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    removeRepeatedPosition i (insertRepeatedPosition i x) = x := by
  ext j
  simp [removeRepeatedPosition, insertRepeatedPosition]

/-- The reverse direction of the repeated-position pushforward formula:
restricting a vector after inserting the repeated coordinate recovers the
original measure. -/
lemma measurable_insertRepeatedPosition {n : ℕ} (i : Fin (n + 1)) :
    Measurable (@insertRepeatedPosition n i) := by
  change Measurable
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) i.succ).symm ∘
      fun x : Fin (n + 1) → ℝ => (x i, x))
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) i.succ).symm.measurable.comp
    ((measurable_pi_apply i).prodMk measurable_id)

lemma map_removeRepeatedPosition_insertRepeatedPosition {n : ℕ}
    (i : Fin (n + 1)) (M : Measure (Fin (n + 1) → ℝ)) :
    (M.map (insertRepeatedPosition i)).map (removeRepeatedPosition i) = M := by
  rw [Measure.map_map (measurable_removeRepeatedPosition i)
    (measurable_insertRepeatedPosition i)]
  rw [show removeRepeatedPosition i ∘ insertRepeatedPosition i = id by
    funext x
    exact removeRepeatedPosition_insertRepeatedPosition i x]
  exact Measure.map_id

/-- On vectors with equal adjacent coordinates, reinserting after restriction
recovers the original vector. -/
lemma insertRepeatedPosition_removeRepeatedPosition_of_diagonal {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 2) → ℝ)
    (hdiag : x i.castSucc = x i.succ) :
    insertRepeatedPosition i (removeRepeatedPosition i x) = x := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i.succ j with rfl | ⟨j, rfl⟩
  · simp [insertRepeatedPosition, removeRepeatedPosition, hdiag]
  · simp [insertRepeatedPosition, removeRepeatedPosition]

/-- The other direction of the repeated-position pushforward formula holds
for measures concentrated on the diagonal where the adjacent coordinates
agree. -/
lemma map_insertRepeatedPosition_removeRepeatedPosition_of_ae_diagonal
    {n : ℕ} (i : Fin (n + 1)) (M : Measure (Fin (n + 2) → ℝ))
    (hdiag : ∀ᵐ x ∂M, x i.castSucc = x i.succ) :
    (M.map (removeRepeatedPosition i)).map (insertRepeatedPosition i) = M := by
  have hcomp : insertRepeatedPosition i ∘ removeRepeatedPosition i =ᵐ[M] id := by
    filter_upwards [hdiag] with x hx
    exact insertRepeatedPosition_removeRepeatedPosition_of_diagonal i x hx
  calc
    (M.map (removeRepeatedPosition i)).map (insertRepeatedPosition i) =
        M.map (insertRepeatedPosition i ∘ removeRepeatedPosition i) :=
      Measure.map_map (measurable_insertRepeatedPosition i)
        (measurable_removeRepeatedPosition i)
    _ = M.map id := Measure.map_congr hcomp
    _ = M := Measure.map_id

/-- Delete the endpoint immediately after a repeated edge. -/
def deleteRepeatedPointGrid {n : ℕ} (i : Fin (n + 1))
    (grid : Fin (n + 2) → unitInterval) : Fin (n + 1) → unitInterval :=
  fun j => grid ((i.succ).succAbove j)

lemma deleteRepeatedPointGrid_monotone {n : ℕ} (i : Fin (n + 1))
    (grid : Fin (n + 2) → unitInterval) (hgrid : Monotone grid) :
    Monotone (deleteRepeatedPointGrid i grid) := by
  exact hgrid.comp (i.succ).succAboveOrderEmb.monotone

lemma deleteRepeatedPointGrid_start {n : ℕ} (i : Fin (n + 1))
    (grid : Fin (n + 2) → unitInterval) (hstart : grid 0 = ⊥) :
    deleteRepeatedPointGrid i grid 0 = ⊥ := by
  change grid ((i.succ).succAbove 0) = ⊥
  rw [Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i), hstart]

lemma denseEvaluation_insertRepeatedPoint {n : ℕ}
    (i : Fin (n + 1)) (grid : Fin (n + 2) → unitInterval)
    (hrep : grid i.castSucc = grid i.succ) (f : CadlagPath unitInterval ℝ) :
    denseEvaluation grid f =
      insertRepeatedPosition i (denseEvaluation (deleteRepeatedPointGrid i grid) f) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i.succ j with rfl | ⟨j, rfl⟩
  · simp [denseEvaluation, insertRepeatedPosition, deleteRepeatedPointGrid, hrep]
  · simp [denseEvaluation, insertRepeatedPosition, deleteRepeatedPointGrid]

lemma deleteRepeatedPointGrid_increment_interval {n : ℕ}
    (i : Fin (n + 1)) (grid : Fin (n + 2) → unitInterval)
    (hrep : grid i.castSucc = grid i.succ) (j : Fin n) :
    ((deleteRepeatedPointGrid i grid j.succ : unitInterval) : ℝ) -
        (deleteRepeatedPointGrid i grid j.castSucc : unitInterval) =
      ((grid (i.succAbove j).succ : unitInterval) : ℝ) -
        (grid (i.succAbove j).castSucc : unitInterval) := by
  have hlower :
      deleteRepeatedPointGrid i grid j.castSucc = grid (i.succAbove j).castSucc := by
    by_cases hlt : j.val < i.val
    · have hleft : (i.succ).succAbove j.castSucc = j.castSucc.castSucc := by
        exact Fin.succAbove_of_castSucc_lt _ _ (Fin.mk_lt_mk.mpr (by
          simpa only [Fin.val_castSucc, Fin.val_succ] using Nat.lt_succ_of_lt hlt))
      have hright : i.succAbove j = j.castSucc :=
        Fin.succAbove_of_castSucc_lt i j (Fin.mk_lt_mk.mpr hlt)
      rw [deleteRepeatedPointGrid, hleft, hright]
    · by_cases heq : j.val = i.val
      · have hj : j.castSucc = i := Fin.ext heq
        have hleft : (i.succ).succAbove j.castSucc = i.castSucc := by
          have hlt : j.castSucc.castSucc < i.succ := by
            rw [hj]
            exact Fin.mk_lt_mk.mpr (by simp)
          rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
          simpa using congrArg Fin.castSucc hj
        have hright : i.succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc i j (by simp [← hj])
        rw [deleteRepeatedPointGrid, hleft, hright]
        have hrightidx : j.succ.castSucc = i.succ := Fin.ext (by simpa using heq)
        rw [hrightidx]
        exact hrep
      · have hgt : i.val < j.val := by omega
        have hleft : (i.succ).succAbove j.castSucc = j.succ.castSucc := by
          calc
            (i.succ).succAbove j.castSucc = j.castSucc.succ :=
              Fin.succAbove_of_le_castSucc _ _ (Fin.mk_le_mk.mpr (by
                simpa only [Fin.val_succ, Fin.val_castSucc] using Nat.succ_le_of_lt hgt))
            _ = j.succ.castSucc := by
              apply Fin.ext
              simp only [Fin.val_succ, Fin.val_castSucc]
        have hright : i.succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc i j (Fin.mk_le_mk.mpr hgt.le)
        rw [deleteRepeatedPointGrid, hleft, hright]
  have hupper : (deleteRepeatedPointGrid i grid j.succ : unitInterval) =
      grid (i.succAbove j).succ := by
    simp [deleteRepeatedPointGrid, Fin.succ_succAbove_succ]
  rw [hupper, hlower]

lemma contractNth_insertZeroCoordinate {n : ℕ} (i : Fin (n + 1))
    (x : Fin n → ℝ) :
    Fin.contractNth i (· + ·) (insertZeroCoordinate i x) = x := by
  ext j
  rcases lt_trichotomy j.val i.val with hlt | heq | hgt
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ hlt]
    have hidx : i.succAbove j = j.castSucc :=
      Fin.succAbove_of_castSucc_lt i j (Fin.mk_lt_mk.mpr hlt)
    rw [← hidx]
    simp [insertZeroCoordinate]
  · have hji : j.castSucc = i := Fin.ext heq
    rw [Fin.contractNth_apply_of_eq _ _ _ _ heq]
    have hidx : i.succAbove j = j.succ :=
      Fin.succAbove_of_le_castSucc i j (by simp [← hji])
    rw [← hidx]
    simp [insertZeroCoordinate, hji]
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ hgt]
    have hidx : i.succAbove j = j.succ :=
      Fin.succAbove_of_le_castSucc i j (Fin.mk_le_mk.mpr hgt.le)
    rw [← hidx]
    simp [insertZeroCoordinate]

/-- Partial sums commute with reinserting a zero increment: the corresponding
position coordinate is repeated. -/
lemma partialSum_insertZeroCoordinate {n : ℕ} (i : Fin (n + 1))
    (x : Fin n → ℝ) :
    Fin.partialSum (insertZeroCoordinate i x) =
      insertRepeatedPosition i (Fin.partialSum x) := by
  have hcontract := congrArg Fin.partialSum (contractNth_insertZeroCoordinate i x)
  rw [Fin.partialSum_contractNth] at hcontract
  have hzero : insertZeroCoordinate i x i = 0 := by
    simp [insertZeroCoordinate]
  have hbefore : Fin.partialSum (insertZeroCoordinate i x) i.castSucc =
      Fin.partialSum x i := by
    simpa using congrFun hcontract i
  funext j
  rcases Fin.eq_self_or_eq_succAbove i.succ j with rfl | ⟨j', rfl⟩
  · have hzero : insertZeroCoordinate i x i = 0 := by
      simp [insertZeroCoordinate]
    simp [insertRepeatedPosition, Fin.partialSum_succ, hzero, hbefore]
  · have h := congrFun hcontract j'
    simpa [insertRepeatedPosition] using h

/-- Reinsert a Dirac-zero factor into a finite product measure. This is the
measure-theoretic step used when a repeated grid point is restored. -/
lemma measure_pi_insertZeroCoordinate {n : ℕ} (i : Fin (n + 1))
    (μ : Fin n → Measure ℝ) (ν : Fin (n + 1) → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] [∀ j, SigmaFinite (ν j)]
    (hzero : ν i = Measure.dirac 0)
    (hrest : ∀ j : Fin n, ν (i.succAbove j) = μ j) :
    Measure.pi ν = (Measure.pi μ).map (insertZeroCoordinate i) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hsplit := MeasureTheory.measurePreserving_piFinSuccAbove ν i
  have hrestFun : (fun j : Fin n => ν (i.succAbove j)) = μ := funext hrest
  rw [← hsplit.symm.map_eq, hzero, hrestFun, Measure.dirac_prod,
    Measure.map_map e.symm.measurable (by fun_prop)]
  rfl

/-- The strict-grid position laws already force the path to start at zero:
apply the zero-dimensional law to the singleton grid at `⊥`. -/
lemma ae_start_eq_zero_of_strictGridPositionLaws
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hStrict : ∀ (n : ℕ) (grid : Fin (n + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ →
      P.map (denseEvaluation grid) =
        ((stableTimeLawProductProbability (μ := μ) α grid :
          ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)).map
            (Fin.partialSum : (Fin n → ℝ) → (Fin (n + 1) → ℝ))) :
    ∀ᵐ f ∂P, f ⊥ = 0 := by
  let grid : Fin 1 → unitInterval := fun _ => ⊥
  have hgrid : StrictMono grid := by
    intro i j hij
    have : i = j := Subsingleton.elim _ _
    subst j
    exact False.elim (lt_irrefl i hij)
  have hpos := hStrict 0 grid hgrid (by simp [grid])
  have hmap : P.map (fun f : CadlagPath unitInterval ℝ => f ⊥) = Measure.dirac 0 := by
    calc
      P.map (fun f : CadlagPath unitInterval ℝ => f ⊥) =
          (P.map (denseEvaluation grid)).map (Function.eval (0 : Fin 1)) := by
            rw [Measure.map_map (by fun_prop) (measurable_denseEvaluation grid)]
            rfl
      _ = (((stableTimeLawProductProbability (μ := μ) α grid :
          ProbabilityMeasure (Fin 0 → ℝ)) : Measure (Fin 0 → ℝ)).map
            (Fin.partialSum : (Fin 0 → ℝ) → (Fin 1 → ℝ))).map
              (Function.eval (0 : Fin 1)) := by rw [hpos]
      _ = Measure.dirac 0 := by
        have hL : (stableTimeLawProductProbability (μ := μ) α grid :
            Measure (Fin 0 → ℝ)) = Measure.dirac (fun _ : Fin 0 => (0 : ℝ)) := by
          change Measure.pi (fun j : Fin 0 => stableTimeLaw α μ
            ((grid j.succ : unitInterval) - (grid j.castSucc : unitInterval))) = _
          exact Measure.pi_of_empty _ _
        rw [hL]
        simp [Fin.partialSum]
  have hlaw : HasLaw (fun f : CadlagPath unitInterval ℝ => f ⊥)
      (Measure.dirac 0) P := ⟨(Skorokhod.measurable_apply ⊥).aemeasurable, hmap⟩
  exact hlaw.ae_eq_of_dirac

end ProbabilityTheory.StablePathLaw.MonotoneGrid.Lemmas

end
