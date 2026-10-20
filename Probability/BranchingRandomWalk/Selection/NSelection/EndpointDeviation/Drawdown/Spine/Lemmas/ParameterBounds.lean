/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.LogScales
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Window
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.Tube

/-!
# Parameter selection and endpoint-envelope estimates

This module contains non-reusable intermediate statements in the proof of
the positive-initial-mass capacity estimate, Proposition 3.1, equation
(4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the
complete graph*, arXiv:2512.23266 (2025). The preceding module in the
`Lemmas/` chain supplies the definitions and estimates used here.

The declarations are theorem-specific reductions: they pass from the
restarted tube data to the estimates needed by the next stage of the proof.
Reusable path-event and measure inequalities remain in their semantic
modules outside this directory.

## Proof-chain statements

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_rightTailPositiveAParameters` chooses $b,v,c$ satisfying the strict threshold and width inequalities required by the positive-parameter construction.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveADrift_le_span`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveAWindowUpper_at_cutoff`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveAFirstStageUpper_le_zero`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveAWindowUpper_le_generationDrift_add_width`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveADrift_eq_ahExponent` bound the schedule $d_j=(\kappa/c^2)D^{-2/3}j$ and the exponential endpoint weights by their terminal or generation-scale envelopes.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveAWindowWeightedAH_le` and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveADrift_le_shortPrefix_power` compare the weighted long-prefix and short-prefix terms with the Aïdékon--Hu exponent.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.sum_fin_if_le_eq_add_mul` splits a finite sum at $\ell$, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveA_canceledAH_sum_le` bounds the resulting sum by $(\ell+1)+D\exp((-b+v)\log N+cD^{1/3}+\kappa c^pD^{p/3})$.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The parameter inequalities in the positive-`a` construction are feasible
whenever the target threshold is strictly above the limiting trajectory.
Here `r` is the positive cube root of `t`; keeping `r^3 = t` explicit makes
the algebraic choice of `c` transparent. -/
lemma exists_rightTailPositiveAParameters
    (a t r sigmaSq zeta : ℝ)
    (ha : 0 < a) (ht : 0 < t) (hr : 0 < r) (hrcube : r ^ 3 = t)
    (hsigma : 0 ≤ sigmaSq)
    (hgap : -a + Real.pi ^ 2 / 2 * sigmaSq * t < zeta) :
    ∃ b v c : ℝ,
      0 < b ∧ b < a ∧ 0 < v ∧ v < b ∧ v ≤ c ∧ 0 < c ∧ c < r⁻¹ ∧
      c * r + (a - b) + v < 1 ∧
      -b + Real.pi ^ 2 / 2 * sigmaSq * (c⁻¹ ^ 2 * r) +
        2 * v * (1 + r) < zeta := by
  let C : ℝ := Real.pi ^ 2 / 2 * sigmaSq
  let gap : ℝ := zeta - (-a + C * t)
  let K : ℝ := 1 / 3 + 8 * C * t + 2 / 3 * (1 + r)
  let δ₀ : ℝ := min (min (1 / 2) a) (gap / (2 * K))
  let δ : ℝ := min δ₀ (1 / (4 * r))
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
    dsimp [δ, δ₀]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδA : δ ≤ a := by
    dsimp [δ, δ₀]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδGap : δ ≤ gap / (2 * K) := by
    dsimp [δ, δ₀]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hδSmall : δ ≤ 1 / (4 * r) := by
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
  refine ⟨b, v, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [b]
    nlinarith [ha, hδA]
  · dsimp [b]
    linarith
  · dsimp [v]
    positivity
  · dsimp [b, v]
    nlinarith [ha, hδA]
  · dsimp [v, c]
    have hδr : δ * r ≤ 1 / 4 := by
      have hδr4 : δ * (4 * r) ≤ 1 :=
        (le_div_iff₀ (by positivity : 0 < 4 * r)).mp hδSmall
      nlinarith [hδr4]
    have hvrt : (δ / 3) * r ≤ 1 / 12 := by nlinarith [hδr]
    apply (le_div_iff₀ hr).2
    nlinarith [hvrt, hδHalf]
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

/-- The drift at any time in the second tube is bounded by its terminal
diffusive scale. -/
lemma rightTailPositiveADrift_le_span
    (ell ellN j : ℕ) (κ c : ℝ)
    (hell : ell < ellN) (hκ : 0 ≤ κ)
    (hj : j ≤ ellN - ell) :
    rightTailPositiveADrift ell ellN κ c j ≤
      κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
  let span : ℝ := ((ellN - ell : ℕ) : ℝ)
  have hspan : 0 < span := by
    dsimp [span]
    exact_mod_cast Nat.sub_pos_of_lt hell
  have hjReal : (j : ℝ) ≤ span := by
    dsimp [span]
    exact_mod_cast hj
  have hpow : span ^ ((-2 : ℝ) / 3) * span = span ^ (3⁻¹ : ℝ) := by
    calc
      span ^ ((-2 : ℝ) / 3) * span =
          span ^ ((-2 : ℝ) / 3) * span ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = span ^ (((-2 : ℝ) / 3) + 1) := by rw [← Real.rpow_add hspan]
      _ = span ^ (3⁻¹ : ℝ) := by congr 1; norm_num
  have hcoeff : 0 ≤ κ / c ^ 2 := div_nonneg hκ (sq_nonneg c)
  calc
    rightTailPositiveADrift ell ellN κ c j =
        κ / c ^ 2 * (span ^ ((-2 : ℝ) / 3) * (j : ℝ)) := by
          simp [rightTailPositiveADrift, span]
          ring
    _ ≤ κ / c ^ 2 * (span ^ ((-2 : ℝ) / 3) * span) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjReal (Real.rpow_nonneg hspan.le _)) hcoeff
    _ = κ / c ^ 2 * span ^ (3⁻¹ : ℝ) := by rw [hpow]

/-- The endpoint of the first tube is its prescribed narrow interval. -/
lemma rightTailPositiveAWindowUpper_at_cutoff
    (ell ellN : ℕ) (logN b v c κ : ℝ) :
    rightTailPositiveAWindowUpper ell ellN logN b v c κ ell =
      (-b + v) * logN := by
  simp [rightTailPositiveAWindowUpper]

/-- The first-stage endpoint envelope is nonpositive when the narrow terminal
window lies below zero. -/
lemma rightTailPositiveAFirstStageUpper_le_zero
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hvb : v ≤ b) (hlog : 0 ≤ logN)
    (k : ℕ) (hk : k ≤ ell) :
    rightTailPositiveAWindowUpper ell ellN logN b v c κ k ≤ 0 := by
  by_cases hklt : k < ell
  · simp [rightTailPositiveAWindowUpper, hklt]
  · have hkeq : k = ell := by omega
    rw [hkeq, rightTailPositiveAWindowUpper_at_cutoff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog

/-- At a fixed second-stage generation, the endpoint weight uses that
generation's drift rather than the terminal drift. This pointwise form is
what allows the branching weight to cancel the small-deviation exponent. -/
lemma rightTailPositiveAWindowUpper_le_generationDrift_add_width
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hellN : ell < ellN) (hvc : v ≤ c)
    (hk : ell < k) (hkN : k ≤ ellN) :
    rightTailPositiveAWindowUpper ell ellN logN b v c κ k ≤
      rightTailPositiveADrift ell ellN κ c (k - ell) +
        c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
  have hwidth : 0 ≤ (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
    apply Real.rpow_nonneg
    positivity
  by_cases hend : k = ellN
  · subst k
    have hnotlt : ¬ellN < ell := Nat.not_lt_of_ge hellN.le
    have hne : ellN ≠ ell := by omega
    simp [rightTailPositiveAWindowUpper, hnotlt, hne]
    exact mul_le_mul_of_nonneg_right hvc hwidth
  · have hklt : k < ellN := by omega
    have hnotlt : ¬k < ell := Nat.not_lt_of_ge hk.le
    have hne : k ≠ ell := ne_of_gt hk
    simp [rightTailPositiveAWindowUpper, hnotlt, hne, hklt]

/-- When the tube drift coefficient equals the Aïdékon--Hu rate coefficient,
the generation's deterministic drift exactly cancels the exponential
small-deviation cost at that generation. -/
lemma rightTailPositiveADrift_eq_ahExponent
    (ell ellN d : ℕ) (κ c target sigma : ℝ)
    (hellN : ell < ellN) (hc : 0 < c)
    (hκ : κ = target * sigma ^ 2) :
    rightTailPositiveADrift ell ellN κ c d =
      target * sigma ^ 2 * (d : ℝ) /
        (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2 := by
  let D : ℝ := ((ellN - ell : ℕ) : ℝ)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast Nat.sub_pos_of_lt hellN
  have hrootSq : (D ^ (3⁻¹ : ℝ)) ^ 2 = D ^ ((2 : ℝ) / 3) := by
    calc
      (D ^ (3⁻¹ : ℝ)) ^ 2 = (D ^ (3⁻¹ : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = D ^ ((3⁻¹ : ℝ) * 2) := by rw [← Real.rpow_mul hDpos.le]
      _ = D ^ ((2 : ℝ) / 3) := by congr 1 <;> norm_num
  have hwidthSq : (c * D ^ (3⁻¹ : ℝ)) ^ 2 = c ^ 2 * D ^ ((2 : ℝ) / 3) := by
    rw [mul_pow, hrootSq]
  have hDneg : D ^ ((-2 : ℝ) / 3) = (D ^ ((2 : ℝ) / 3))⁻¹ := by
    have hexponent : (-2 : ℝ) / 3 = -((2 : ℝ) / 3) := by ring
    rw [hexponent, Real.rpow_neg hDpos.le]
  change κ / c ^ 2 * D ^ ((-2 : ℝ) / 3) * (d : ℝ) =
    target * sigma ^ 2 * (d : ℝ) / (c * D ^ (3⁻¹ : ℝ)) ^ 2
  rw [hκ, hwidthSq, hDneg]
  field_simp [hc.ne', ne_of_gt hDpos]

/-- Multiplying the generation-specific endpoint weight by its long-prefix
Aïdékon--Hu probability removes the deterministic drift and leaves only the
initial offset and tube width. -/
lemma rightTailPositiveAWindowWeightedAH_le
    (ell ellN k : ℕ) (logN b v c κ target sigma : ℝ)
    (hellN : ell < ellN) (hvc : v ≤ c) (hc : 0 < c)
    (hk : ell < k) (hkN : k ≤ ellN)
    (hκ : κ = target * sigma ^ 2) :
    ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ k)) *
      ENNReal.ofReal (Real.exp
        (-target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) /
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) ≤
    ENNReal.ofReal (Real.exp
      ((-b + v) * logN + c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) := by
  have hcancel := rightTailPositiveADrift_eq_ahExponent
    ell ellN (k - ell) κ c target sigma hellN hc hκ
  have hupper := rightTailPositiveAWindowUpper_le_generationDrift_add_width
    ell ellN k logN b v c κ hellN hvc hk hkN
  have hcutoff := rightTailPositiveAWindowUpper_at_cutoff ell ellN logN b v c κ
  have hnegative :
      -target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) /
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2 =
        -rightTailPositiveADrift ell ellN κ c (k - ell) := by
    rw [hcancel]
    ring
  have hexponent :
      rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ k +
        (-target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) /
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2) ≤
      (-b + v) * logN + c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
    rw [hcutoff]
    calc
      _ ≤ (-b + v) * logN +
          (rightTailPositiveADrift ell ellN κ c (k - ell) +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) +
          (-target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) /
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2) := by
          linarith
      _ = (-b + v) * logN +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
          rw [hnegative]
          ring
  calc
    _ = ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ k +
          (-target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) /
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    _ ≤ ENNReal.ofReal (Real.exp
        ((-b + v) * logN + c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)

/-- Even before a prefix is long enough for the Aïdékon--Hu estimate, its
drift is small: below the AH cutoff it is at most a constant times
`span^(p/3)`, which is lower order than the tube width when `p < 1`. -/
lemma rightTailPositiveADrift_le_shortPrefix_power
    (ell ellN d : ℕ) (κ c p : ℝ)
    (hellN : ell < ellN) (hκ : 0 ≤ κ) (hc : 0 < c)
    (hshort : (d : ℝ) ≤
      (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p)) :
    rightTailPositiveADrift ell ellN κ c d ≤
      κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3)) := by
  let D : ℝ := ((ellN - ell : ℕ) : ℝ)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast Nat.sub_pos_of_lt hellN
  have hwidthPow :
      (c * D ^ (3⁻¹ : ℝ)) ^ (2 + p) =
        c ^ (2 + p) * D ^ ((2 + p) / 3) := by
    rw [Real.mul_rpow hc.le (by positivity)]
    rw [← Real.rpow_mul hDpos.le]
    congr 1
    ring_nf
  have hcPow : c ^ (2 + p) = c ^ (2 : ℝ) * c ^ p :=
    Real.rpow_add hc 2 p
  have hcPowTwo : c ^ (2 : ℝ) = c ^ 2 := Real.rpow_natCast c 2
  have hDpow :
      D ^ ((-2 : ℝ) / 3) * D ^ ((2 + p) / 3) = D ^ (p / 3) := by
    rw [← Real.rpow_add hDpos]
    congr 1
    ring
  change κ / c ^ 2 * D ^ ((-2 : ℝ) / 3) * (d : ℝ) ≤
    κ * c ^ p * D ^ (p / 3)
  have hshort' := mul_le_mul_of_nonneg_left hshort
    (Real.rpow_nonneg hDpos.le ((-2 : ℝ) / 3))
  calc
    _ = κ / c ^ 2 * (D ^ ((-2 : ℝ) / 3) * (d : ℝ)) := by ring
    _ ≤ κ / c ^ 2 *
        (D ^ ((-2 : ℝ) / 3) * (c * D ^ (3⁻¹ : ℝ)) ^ (2 + p)) :=
          mul_le_mul_of_nonneg_left hshort' (div_nonneg hκ (sq_nonneg c))
    _ = κ * c ^ p * D ^ (p / 3) := by
          rw [hwidthPow, hcPow, hcPowTwo]
          calc
            κ / c ^ 2 *
                (D ^ ((-2 : ℝ) / 3) * (c ^ 2 * c ^ p * D ^ ((2 + p) / 3))) =
              κ / c ^ 2 *
                (c ^ 2 * c ^ p *
                  (D ^ ((-2 : ℝ) / 3) * D ^ ((2 + p) / 3))) := by ring
            _ = κ * c ^ p * D ^ (p / 3) := by
              rw [hDpow]
              field_simp [hc.ne']

/-- The canceled two-stage AH sum has only the original first-phase count
plus a second-phase contribution with exponent
`(-b+v) logN + c L^(1/3) + O(L^(p/3))`. -/
lemma sum_fin_if_le_eq_add_mul (ell ellN : ℕ) (A B : ℝ≥0∞)
    (hell : ell ≤ ellN) :
    (∑ k : Fin (ellN + 1), if (k : ℕ) ≤ ell then A else B) =
      ((ell + 1 : ℕ) : ℝ≥0∞) * A +
        ((ellN - ell : ℕ) : ℝ≥0∞) * B := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≤ ell then A else B)]
  rw [← Finset.sum_range_add_sum_Ico
    (fun k : ℕ => if k ≤ ell then A else B)
    (show ell + 1 ≤ ellN + 1 by omega)]
  have hfirst :
      (∑ k ∈ Finset.range (ell + 1), if k ≤ ell then A else B) =
        ((ell + 1 : ℕ) : ℝ≥0∞) * A := by
    have hterm : ∀ k ∈ Finset.range (ell + 1), (if k ≤ ell then A else B) = A := by
      intro k hk
      have hk' : k < ell + 1 := Finset.mem_range.mp hk
      simp [Nat.lt_succ_iff.mp hk']
    rw [Finset.sum_congr rfl hterm]
    simp [Finset.sum_const]
  have hsecond :
      (∑ k ∈ Finset.Ico (ell + 1) (ellN + 1), if k ≤ ell then A else B) =
        ((ellN - ell : ℕ) : ℝ≥0∞) * B := by
    have hterm : ∀ k ∈ Finset.Ico (ell + 1) (ellN + 1),
        (if k ≤ ell then A else B) = B := by
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      simp [Nat.not_le_of_gt hk'.1]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlength : ellN + 1 - (ell + 1) = ellN - ell := by omega
    rw [hlength]
    simp [Finset.sum_const]
  rw [hfirst, hsecond]

lemma rightTailPositiveA_canceledAH_sum_le
    (ell ellN : ℕ) (logN b v c κ p : ℝ)
    (hellN : ell < ellN) (hκ : 0 ≤ κ) (hc : 0 < c)
    (hvc : v ≤ c) :
    (∑ k : Fin (ellN + 1),
      if (k : ℕ) ≤ ell then 1 else
        if (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤
            (((k : ℕ) - ell : ℕ) : ℝ) then
          ENNReal.ofReal (Real.exp
            ((-b + v) * logN +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))))
        else ENNReal.ofReal (Real.exp
          (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
            rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)))) ≤
      ((ell + 1 : ℕ) : ℝ≥0∞) +
        ((ellN - ell : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp
            ((-b + v) * logN +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
              κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3)))) := by
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  let lowOrder : ℝ := κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))
  have hlowOrder : 0 ≤ lowOrder := by
    dsimp [lowOrder]
    positivity
  have hsum :
      (∑ k : Fin (ellN + 1),
        if (k : ℕ) ≤ ell then 1 else
          if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
            ENNReal.ofReal (Real.exp ((-b + v) * logN + width))
          else ENNReal.ofReal (Real.exp
            (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
              rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)))) ≤
      ∑ k : Fin (ellN + 1),
        if (k : ℕ) ≤ ell then 1 else
          ENNReal.ofReal (Real.exp ((-b + v) * logN + width + lowOrder)) := by
    apply Finset.sum_le_sum
    intro k _hk
    by_cases hkle : (k : ℕ) ≤ ell
    · simp [hkle]
    · have hk : ell < (k : ℕ) := Nat.lt_of_not_ge hkle
      have hkN : (k : ℕ) ≤ ellN := Nat.le_of_lt_succ k.isLt
      by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
      · have hweight :
            ENNReal.ofReal (Real.exp ((-b + v) * logN + width)) ≤
              ENNReal.ofReal (Real.exp ((-b + v) * logN + width + lowOrder)) := by
          apply ENNReal.ofReal_le_ofReal
          exact Real.exp_le_exp.mpr (by linarith [hlowOrder])
        simpa [hkle, hlong, width, lowOrder] using hweight
      · have hd : (((k : ℕ) - ell : ℕ) : ℝ) ≤ width ^ (2 + p) :=
          le_of_not_ge hlong
        have hdrift := rightTailPositiveADrift_le_shortPrefix_power
          ell ellN ((k : ℕ) - ell) κ c p hellN hκ hc (by
            simpa [width] using hd)
        have hupper := rightTailPositiveAWindowUpper_le_generationDrift_add_width
          ell ellN (k : ℕ) logN b v c κ hellN hvc hk hkN
        have hcutoff := rightTailPositiveAWindowUpper_at_cutoff
          ell ellN logN b v c κ
        have hexponent :
            rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ) ≤
              (-b + v) * logN + width + lowOrder := by
          rw [hcutoff]
          dsimp [width, lowOrder]
          linarith
        simpa [hkle, hlong] using ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.mpr hexponent)
  calc
    _ ≤ ∑ k : Fin (ellN + 1),
        if (k : ℕ) ≤ ell then 1 else
          ENNReal.ofReal (Real.exp ((-b + v) * logN + width + lowOrder)) := by
            simpa [width, lowOrder] using hsum
    _ = ((ell + 1 : ℕ) : ℝ≥0∞) * 1 +
        ((ellN - ell : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp ((-b + v) * logN + width + lowOrder)) :=
          sum_fin_if_le_eq_add_mul ell ellN 1
            (ENNReal.ofReal (Real.exp ((-b + v) * logN + width + lowOrder)))
            (Nat.le_of_lt hellN)
    _ = ((ell + 1 : ℕ) : ℝ≥0∞) +
        ((ellN - ell : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp ((-b + v) * logN + width + lowOrder)) := by
            simp
    _ = _ := by simp [width, lowOrder]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
