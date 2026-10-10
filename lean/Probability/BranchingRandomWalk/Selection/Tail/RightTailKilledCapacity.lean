/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.CapacitySpine
import Probability.Process.RandomWalk.Path.Restart.Basic

/-!
# A killed population for the positive-initial-mass right-tail argument

The two tube stages in the proof of (4.15) are represented by one restarted
window schedule.  The recursively retained population is constructed from the
pre-sampled branching field.  Its capacity-failure probability is bounded by
actual tilted-walk corridor probabilities through the first-moment and
Markov interfaces.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- Drift of the second-stage tube in the positive-`a` proof of (4.15),
with `κ = π² σ² / 2`. -/
noncomputable def rightTailPositiveADrift
    (ell ellN : ℕ) (κ c : ℝ) (j : ℕ) : ℝ :=
  κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ ((-2 : ℝ) / 3)) * (j : ℝ)

/-- Restarted path windows for the killed population used in the proof of
(4.15). Up to `ell`, paths remain in `[-b log N, 0]`, with a narrower window
at `ell`. The next stage uses the tilted tube, with a narrower terminal
window at `ellN`. -/
noncomputable def rightTailPositiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : Set ℝ :=
  if k < ell then Set.Icc (-b * logN) 0
  else if k = ell then Set.Icc (-b * logN) ((-b + v) * logN)
  else if k < ellN then
    Set.Icc (rightTailPositiveADrift ell ellN κ c (k - ell))
      (rightTailPositiveADrift ell ellN κ c (k - ell) +
        c * (((ellN - ell : ℕ) : ℝ) ^ (1 / 3 : ℝ)))
  else if k = ellN then
    Set.Icc (rightTailPositiveADrift ell ellN κ c (ellN - ell))
      (rightTailPositiveADrift ell ellN κ c (ellN - ell) +
        v * (((ellN - ell : ℕ) : ℝ) ^ (1 / 3 : ℝ)))
  else ∅

/-- Deterministic upper endpoint for each stage window. -/
noncomputable def rightTailPositiveAWindowUpper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) : ℝ :=
  if k < ell then 0
  else if k = ell then (-b + v) * logN
  else if k < ellN then
    rightTailPositiveADrift ell ellN κ c (k - ell) +
      c * (((ellN - ell : ℕ) : ℝ) ^ (1 / 3 : ℝ))
  else if k = ellN then
    rightTailPositiveADrift ell ellN κ c (ellN - ell) +
      v * (((ellN - ell : ℕ) : ℝ) ^ (1 / 3 : ℝ))
  else 0

/-- The parameter inequalities in the positive-`a` construction are feasible
whenever the target threshold is strictly above the limiting trajectory.
Here `r` is the positive cube root of `t`; keeping `r^3 = t` explicit makes
the algebraic choice of `c` transparent. -/
theorem exists_rightTailPositiveAParameters
    (a t r sigmaSq zeta : ℝ)
    (ha : 0 < a) (ht : 0 < t) (hr : 0 < r) (hrcube : r ^ 3 = t)
    (hsigma : 0 ≤ sigmaSq)
    (hgap : -a + Real.pi ^ 2 / 2 * sigmaSq * t < zeta) :
    ∃ b v c : ℝ,
      0 < b ∧ b < a ∧ 0 < v ∧ 0 < c ∧ c < r⁻¹ ∧
      c * r + (a - b) + v < 1 ∧
      -b + Real.pi ^ 2 / 2 * sigmaSq * (c⁻¹ ^ 2 * r) +
        2 * v * (1 + r) < zeta := by
  let C : ℝ := Real.pi ^ 2 / 2 * sigmaSq
  let gap : ℝ := zeta - (-a + C * t)
  let K : ℝ := 1 / 3 + 8 * C * t + 2 / 3 * (1 + r)
  let δ : ℝ := min (min (1 / 2) a) (gap / (2 * K))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hgapPos : 0 < gap := by
    dsimp [gap, C]
    linarith
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδHalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hδA : δ ≤ a := by
    dsimp [δ]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hδGap : δ ≤ gap / (2 * K) := by
    dsimp [δ]
    exact min_le_right _ _
  have hden : 0 < 1 - δ := by linarith
  have hquadLeft : 0 ≤ 1 - 2 * δ := by linarith
  have hquadRight : 0 ≤ (11 : ℝ) / 2 - 4 * δ := by linarith
  have hquad : 0 ≤ 8 * δ ^ 2 - 15 * δ + 6 := by
    have hprod := mul_nonneg hquadLeft hquadRight
    nlinarith
  have hpolyProduct : 1 ≤ (1 + 8 * δ) * (1 - δ) ^ 2 := by
    have hprod := mul_nonneg hδ.le hquad
    nlinarith
  have hratio : 1 / (1 - δ) ^ 2 ≤ 1 + 8 * δ := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).2
    nlinarith [hpolyProduct]
  have hratioTerm : C * (t / (1 - δ) ^ 2) ≤ C * t * (1 + 8 * δ) := by
    calc
      C * (t / (1 - δ) ^ 2) = (C * t) * (1 / (1 - δ) ^ 2) := by ring
      _ ≤ (C * t) * (1 + 8 * δ) :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hC ht.le)
  let b : ℝ := a - δ / 3
  let v : ℝ := δ / 3
  let c : ℝ := (1 - δ) / r
  have hcInv : c⁻¹ = r / (1 - δ) := by
    dsimp [c]
    field_simp [hr.ne', hden.ne']
  have hcScale : c⁻¹ ^ 2 * r = t / (1 - δ) ^ 2 := by
    rw [hcInv]
    calc
      (r / (1 - δ)) ^ 2 * r = r ^ 3 / (1 - δ) ^ 2 := by
        field_simp [hden.ne']
      _ = t / (1 - δ) ^ 2 := by rw [hrcube]
  have hδK : δ * K ≤ gap / 2 := by
    calc
      δ * K ≤ (gap / (2 * K)) * K :=
        mul_le_mul_of_nonneg_right hδGap hK.le
      _ = gap / 2 := by field_simp [hK.ne']
  refine ⟨b, v, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [b]
    nlinarith [ha, hδA]
  · dsimp [b]
    linarith
  · dsimp [v]
    positivity
  · dsimp [c]
    exact div_pos (by linarith) hr
  · dsimp [c]
    rw [div_lt_iff₀ hr]
    rw [inv_mul_cancel₀ hr.ne']
    linarith
  · dsimp [b, v, c]
    field_simp [hr.ne']
    linarith
  · dsimp [b, v]
    rw [hcScale]
    change -(a - δ / 3) + C * (t / (1 - δ) ^ 2) +
      2 * (δ / 3) * (1 + r) < zeta
    have hmain : -(a - δ / 3) + C * (t / (1 - δ) ^ 2) +
        2 * (δ / 3) * (1 + r) ≤ -a + C * t + δ * K := by
      dsimp [K]
      nlinarith [hratioTerm]
    have hgapEq : -a + C * t + gap = zeta := by
      dsimp [gap]
      ring
    calc
      -(a - δ / 3) + C * (t / (1 - δ) ^ 2) +
          2 * (δ / 3) * (1 + r) ≤ -a + C * t + δ * K := hmain
      _ ≤ -a + C * t + gap / 2 := by linarith [hδK]
      _ < -a + C * t + gap := by linarith [hgapPos]
      _ = zeta := hgapEq

theorem measurableSet_rightTailPositiveARestartedWindow
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    MeasurableSet (rightTailPositiveARestartedWindow ell ellN logN b v c κ k) := by
  classical
  unfold rightTailPositiveARestartedWindow
  split_ifs <;> simp [measurableSet_Icc]

theorem rightTailPositiveARestartedWindow_zero_mem
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hell : 0 < ell) (hb : 0 ≤ b) (hlog : 0 ≤ logN) :
    0 ∈ rightTailPositiveARestartedWindow ell ellN logN b v c κ 0 := by
  simp [rightTailPositiveARestartedWindow, hell, mul_nonneg hb hlog]

theorem rightTailPositiveARestartedWindow_subset_Iic_upper
    (ell ellN : ℕ) (logN b v c κ : ℝ) (k : ℕ) :
    rightTailPositiveARestartedWindow ell ellN logN b v c κ k ⊆
      Set.Iic (rightTailPositiveAWindowUpper ell ellN logN b v c κ k) := by
  classical
  unfold rightTailPositiveARestartedWindow rightTailPositiveAWindowUpper
  split_ifs <;> simp [Set.Icc_subset_Iic_self]

/-- Markov bound for the capacity event of the actual causal killed tree with
the two stages of the positive-`a` construction. The right side is expressed
in terms of tilted random-walk corridor probabilities, so the Mogulskii input
can be supplied separately without assuming any killed-population expectation
bound. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (_hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro p hp
        rcases RootIndexed.mem_initialPopulation_iff.mp hp with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          ENNReal.ofReal (Real.exp
            (if (k : ℕ) ≤ ell then upper k else upper ell + upper k)) *
          RandomWalk.restartedWindowProbability
            (tiltedIncrementFieldLaw realPotential μ) ell window
            (k : ℕ) 0) / (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  let bound : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Real.exp (if k ≤ ell then upper k else upper ell + upper k)) *
      RandomWalk.restartedWindowProbability ν ell window k 0
  have hwindow : ∀ k, MeasurableSet (window k) :=
    measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ
  have hzero : 0 ∈ window 0 :=
    rightTailPositiveARestartedWindow_zero_mem ell ellN logN b v c κ
      hell hb hlog
  have hupper : ∀ k, window k ⊆ Set.Iic (upper k) :=
    rightTailPositiveARestartedWindow_subset_Iic_upper ell ellN logN b v c κ
  have hbound : HasRestartedWindowFirstMomentBound ν ell window Set.univ bound :=
    hasRestartedWindowFirstMomentBound_of_zero_probability ν ell window
      hwindow upper hupper Set.univ
      (fun k => RandomWalk.restartedWindowProbability ν ell window k 0)
      (fun _ => le_rfl)
  simpa [window, upper, ν, RootIndexed.initialPopulation] using
    RootIndexed.CausalPopulation.measure_capacityEvent_compl_le_card_mul_sum_of_windowFirstMomentBound
      (roots := Finset.univ) (initialPosition := fun _ : Fin m => (0 : ℝ))
      (d := id) (hd := measurable_id) (μ := μ) hboundary ell window hwindow
      hzero upper hupper Set.univ bound
      (fun _ _ => Set.mem_univ _) hbound N ellN

/-- Uniform corridor estimates can be substituted directly into the
positive-`a` killed-capacity bound. The endpoint envelope controls the
exponential weight, while a single bound `p` controls every restarted-window
probability. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_uniform
    (m ell ellN N : ℕ) (logN b v c κ U : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (p : ℝ≥0∞)
    (hupper : ∀ k : Fin (ellN + 1),
      (if (k : ℕ) ≤ ell then
        rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)
      else
        rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)) ≤ U)
    (hpath : ∀ k : Fin (ellN + 1),
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ p) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro p hp
        rcases RootIndexed.mem_initialPopulation_iff.mp hp with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ _k : Fin (ellN + 1), ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  have hbase := measure_rightTailPositiveAKilled_capacityEvent_compl_le
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary
  have hsum :
      (∑ k : Fin (ellN + 1),
        ENNReal.ofReal (Real.exp
          (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
          RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0) ≤
        ∑ _k : Fin (ellN + 1), ENNReal.ofReal (Real.exp U) * p := by
    apply Finset.sum_le_sum
    intro k _hk
    have hweight : ENNReal.ofReal (Real.exp
        (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) ≤
        ENNReal.ofReal (Real.exp U) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hupper k))
    calc
      _ ≤ ENNReal.ofReal (Real.exp U) *
          RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0 :=
        mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp U) * p :=
        mul_le_mul_of_nonneg_left (hpath k) (by positivity)
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        ((RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro p hp
            rcases RootIndexed.mem_initialPopulation_iff.mp hp with
              ⟨r, hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)).capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          ENNReal.ofReal (Real.exp
            (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
            RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0) /
          (N + 1 : ℕ) := by
      simpa [window, upper, ν] using hbase
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1), ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)

end ProbabilityTheory.BranchingRandomWalk.Selection.Tail
