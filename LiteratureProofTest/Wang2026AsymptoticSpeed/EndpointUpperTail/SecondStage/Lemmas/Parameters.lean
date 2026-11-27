/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.LogarithmicScales
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.FirstStage.Cutoff
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.Population.RestartedWindow
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

/-!
# Corridor parameters and position bounds

## Internal proof declarations

* `exists_positiveAParameters` chooses $b,v,c$ with capacity margin $1-a+b-v-ct^{1/3}$, and a
  terminal window strictly below $\zeta\log N$ eventually.
* `positiveADrift_eq_rate` rewrites the tube displacement as $\kappa j/w^2$
  for $w=c(H-\ell)^{1/3}$.
* `positiveADrift_le_span` bounds this displacement at any $j\le H-\ell$
  by its terminal value.
* `positiveAWindowUpper_at_cutoff` gives the first-stage terminal upper
  endpoint $(-b+v)\log N$.
* `positiveAFirstStageUpper_le_zero` bounds the first-stage upper endpoint
  by zero under $v\le b$ and $\log N\ge0$.
* `positiveAWindowUpper_le_generationDrift_add_width` gives the
  post-cutoff upper bound $\kappa j/w^2+w$.

These estimates use the parameters of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1, case $0<a<1$.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace LiteratureProofTest.Wang2026AsymptoticSpeed

open ProbabilityTheory

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open Asymptotics

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The parameter inequalities in the positive-`a` construction are feasible
whenever the target threshold is strictly above the limiting trajectory.
Here `r` is the positive cube root of `t`; keeping `r^3 = t` explicit makes
the algebraic choice of `c` transparent. The first-stage success probability is supplied by the logarithmic-corridor survival theorem. -/
lemma exists_positiveAParameters
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
  let K : ℝ := 1 / 2 + 8 * C * t + 1 / 4 * (1 + r)
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
  let b : ℝ := a - δ / 2
  let v : ℝ := δ / 8
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
    nlinarith [ha, hδA, hδ]
  · dsimp [b]
    linarith
  · dsimp [v]
    positivity
  · dsimp [b, v]
    nlinarith [ha, hδA, hδ]
  · dsimp [v, c]
    have hδr : δ * r ≤ 1 / 4 := by
      have hδr4 : δ * (4 * r) ≤ 1 :=
        (le_div_iff₀ (by positivity : 0 < 4 * r)).mp hδSmall
      nlinarith [hδr4]
    have hvrt : (δ / 8) * r ≤ 1 / 32 := by nlinarith [hδr]
    have hcr : 1 / 2 ≤ 1 - δ := by linarith [hδHalf]
    apply (le_div_iff₀ hr).2
    nlinarith [hvrt, hcr]
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
    change -(a - δ / 2) + C * (t / (1 - δ) ^ 2) +
      2 * (δ / 8) * (1 + r) < zeta
    have hmain' : -(a - δ / 2) + C * (t / (1 - δ) ^ 2) +
        2 * (δ / 8) * (1 + r) ≤ -a + C * t + δ * K := by
      dsimp [K]
      nlinarith [hratioTerm]
    have hgapEq : -a + C * t + gap = zeta := by
      dsimp [gap]
      ring
    calc
      -(a - δ / 2) + C * (t / (1 - δ) ^ 2) +
          2 * (δ / 8) * (1 + r) ≤ -a + C * t + δ * K := hmain'
      _ ≤ -a + C * t + gap / 2 := by linarith [hδK]
      _ < -a + C * t + gap := by linarith [hgapPos]
      _ = zeta := hgapEq
/-- The drift at any time in the second tube is bounded by its terminal
diffusive scale. -/
lemma positiveADrift_le_span
    (ell ellN j : ℕ) (κ c : ℝ)
    (hell : ell < ellN) (hκ : 0 ≤ κ)
    (hj : j ≤ ellN - ell) :
    positiveADrift ell ellN κ c j ≤
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
    positiveADrift ell ellN κ c j =
        κ / c ^ 2 * (span ^ ((-2 : ℝ) / 3) * (j : ℝ)) := by
          simp [positiveADrift, span]
          ring
    _ ≤ κ / c ^ 2 * (span ^ ((-2 : ℝ) / 3) * span) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hjReal (Real.rpow_nonneg hspan.le _)) hcoeff
    _ = κ / c ^ 2 * span ^ (3⁻¹ : ℝ) := by rw [hpow]

/-- The endpoint of the first tube is its prescribed narrow interval. -/
lemma positiveAWindowUpper_at_cutoff
    (ell ellN : ℕ) (logN b v c κ : ℝ) :
    positiveAWindowUpper ell ellN logN b v c κ ell =
      (-b + v) * logN := by
  simp [positiveAWindowUpper]

/-- The first-stage endpoint envelope is nonpositive when the narrow terminal
window lies below zero. -/
lemma positiveAFirstStageUpper_le_zero
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hvb : v ≤ b) (hlog : 0 ≤ logN)
    (k : ℕ) (hk : k ≤ ell) :
    positiveAWindowUpper ell ellN logN b v c κ k ≤ 0 := by
  by_cases hklt : k < ell
  · simp [positiveAWindowUpper, hklt]
  · have hkeq : k = ell := by omega
    rw [hkeq, positiveAWindowUpper_at_cutoff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog

/-- At a fixed second-stage generation, the endpoint weight uses that
generation's drift rather than the terminal drift. This pointwise form is
what allows the branching weight to cancel the small-deviation exponent. -/
lemma positiveAWindowUpper_le_generationDrift_add_width
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hellN : ell < ellN) (hvc : v ≤ c)
    (hk : ell < k) (hkN : k ≤ ellN) :
    positiveAWindowUpper ell ellN logN b v c κ k ≤
      positiveADrift ell ellN κ c (k - ell) +
        c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
  have hwidth : 0 ≤ (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
    apply Real.rpow_nonneg
    positivity
  by_cases hend : k = ellN
  · subst k
    have hnotlt : ¬ellN < ell := Nat.not_lt_of_ge hellN.le
    have hne : ellN ≠ ell := by omega
    simp [positiveAWindowUpper, hnotlt, hne]
    exact mul_le_mul_of_nonneg_right hvc hwidth
  · have hklt : k < ellN := by omega
    have hnotlt : ¬k < ell := Nat.not_lt_of_ge hk.le
    have hne : k ≠ ell := ne_of_gt hk
    simp [positiveAWindowUpper, hnotlt, hne, hklt]

/-- The displacement at a relative generation is linear in time with
slope $\kappa/w^2$, where $w$ is the second-stage width. -/
lemma positiveADrift_eq_rate
    (ell ellN d : ℕ) (κ c : ℝ)
    (hellN : ell < ellN) (hc : 0 < c) :
    positiveADrift ell ellN κ c d =
      κ * (d : ℝ) /
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
      _ = D ^ ((2 : ℝ) / 3) := by congr 1; norm_num
  have hwidthSq : (c * D ^ (3⁻¹ : ℝ)) ^ 2 = c ^ 2 * D ^ ((2 : ℝ) / 3) := by
    rw [mul_pow, hrootSq]
  have hDneg : D ^ ((-2 : ℝ) / 3) = (D ^ ((2 : ℝ) / 3))⁻¹ := by
    have hexponent : (-2 : ℝ) / 3 = -((2 : ℝ) / 3) := by ring
    rw [hexponent, Real.rpow_neg hDpos.le]
  change κ / c ^ 2 * D ^ ((-2 : ℝ) / 3) * (d : ℝ) =
    κ * (d : ℝ) / (c * D ^ (3⁻¹ : ℝ)) ^ 2
  rw [hwidthSq, hDneg]
  field_simp [hc.ne', ne_of_gt hDpos]

end LiteratureProofTest.Wang2026AsymptoticSpeed
