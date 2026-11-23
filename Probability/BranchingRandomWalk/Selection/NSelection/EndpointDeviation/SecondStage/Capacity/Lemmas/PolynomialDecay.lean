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
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.FirstStage.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound
import Analysis.Asymptotics.Sequence.ExponentialSum

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Scales
/-!
# Polynomial decay of the capacity overflow probability

## Internal proof declarations

* `eventually_capacityFailure_le_polynomial_of_twoPhaseMomentBound` turns
  a two-phase first-moment bound with exponent margin $a+q<1$ into the
  eventual bound $\mathbb P(\exists j\le H_n,\#P_j>N_n)\le N_n^{-p}$
  for some $p>0$.

Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1, case $0<a<1$.
-/

open Filter
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

/-- The two-phase capacity estimate has polynomial decay when
the initial root count has exponent `a`, the two multiplicity factors have
subexponential size, and the combined exponent `a + q` is below one. -/
lemma eventually_capacityFailure_le_polynomial_of_twoPhaseMomentBound
    {P : ℕ → ℝ≥0∞} {m ell ellN N : ℕ → ℕ} {E : ℕ → ℝ} {a q : ℝ}
    (hN : Tendsto N atTop atTop)
    (horder : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n)
    (hfirstCountLog : Tendsto
      (fun n => Real.log ((ellN n : ℝ) + 1) / Real.log (N n : ℝ))
      atTop (𝓝 0))
    (hspanCountLog : Tendsto
      (fun n => Real.log (((ellN n - ell n : ℕ) : ℝ) + 1) /
        Real.log (N n : ℝ)) atTop (𝓝 0))
    (hERate : Tendsto (fun n => E n / Real.log (N n : ℝ)) atTop (𝓝 q))
    (ha : a < 1) (hmargin : a + q < 1)
    (hm : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hraw : ∀ᶠ n : ℕ in atTop,
      P n ≤ (m n : ℝ≥0∞) *
        (((ell n + 1 : ℕ) : ℝ≥0∞) +
          ((ellN n - ell n : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (E n))) /
        (N n + 1 : ℕ)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      P n ≤ ENNReal.ofReal
        (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let L : ℕ → ℝ := fun n => Real.log (N n : ℝ)
  let D : ℕ → ℕ := fun n => ellN n - ell n
  have hNcast : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hNcast
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hfirstRate : Tendsto
      (fun n => (a * L n + Real.log ((ellN n : ℝ) + 1)) / L n)
      atTop (𝓝 a) := by
    have haConst : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
    have hsum := haConst.add (by simpa [L] using hfirstCountLog)
    have heq : (fun n => (a * L n + Real.log ((ellN n : ℝ) + 1)) / L n)
        =ᶠ[atTop] fun n => a + Real.log ((ellN n : ℝ) + 1) / L n := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  have hsecondRate : Tendsto
      (fun n => (a * L n + Real.log ((D n : ℝ) + 1) + E n) / L n)
      atTop (𝓝 (a + q)) := by
    have haConst : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
    have hsum := (haConst.add (by simpa [L, D] using hspanCountLog)).add
      (by simpa [L] using hERate)
    have heq :
        (fun n => (a * L n + Real.log ((D n : ℝ) + 1) + E n) / L n)
          =ᶠ[atTop] fun n => a + Real.log ((D n : ℝ) + 1) / L n + E n / L n := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  let epsilon : ℝ := min (1 - a) (1 - (a + q)) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hfirstRateGap : a < 1 - 2 * epsilon := by
    dsimp [epsilon]
    have hmin : min (1 - a) (1 - (a + q)) ≤ 1 - a := min_le_left _ _
    linarith
  have hsecondRateGap : a + q < 1 - 2 * epsilon := by
    dsimp [epsilon]
    have hmin : min (1 - a) (1 - (a + q)) ≤ 1 - (a + q) :=
      min_le_right _ _
    linarith
  have hfirstRateEvent : ∀ᶠ n : ℕ in atTop,
      (a * L n + Real.log ((ellN n : ℝ) + 1)) / L n < 1 - 2 * epsilon :=
    hfirstRate.eventually (Iio_mem_nhds hfirstRateGap)
  have hsecondRateEvent : ∀ᶠ n : ℕ in atTop,
      (a * L n + Real.log ((D n : ℝ) + 1) + E n) / L n <
        1 - 2 * epsilon :=
    hsecondRate.eventually (Iio_mem_nhds hsecondRateGap)
  have hfirstRateUniform : ∀ᶠ n : ℕ in atTop,
      (a * L n + Real.log ((ellN n : ℝ) + 1)) / L n <
        (1 - epsilon) - epsilon := by
    filter_upwards [hfirstRateEvent] with n hn
    linarith
  have hsecondRateUniform : ∀ᶠ n : ℕ in atTop,
      (a * L n + Real.log ((D n : ℝ) + 1) + E n) / L n <
        (1 - epsilon) - epsilon := by
    filter_upwards [hsecondRateEvent] with n hn
    linarith
  have hsumExp : ∀ᶠ n : ℕ in atTop,
      Real.exp (a * L n + Real.log ((ellN n : ℝ) + 1)) +
        Real.exp (a * L n + Real.log ((D n : ℝ) + 1) + E n) ≤
          Real.exp ((1 - epsilon) * L n) := by
    have hsum := Asymptotics.eventually_sum_exp_le_exp_mul_of_uniform_gap
      (F := Finset.univ)
      (g := L)
      (e := fun (n : ℕ) (i : Fin 2) =>
        if i.val = 0 then a * L n + Real.log ((ellN n : ℝ) + 1)
        else a * L n + Real.log ((D n : ℝ) + 1) + E n)
      (1 - epsilon) epsilon hepsilon hL (by
        intro i hi
        fin_cases i
        · simpa using hfirstRateUniform
        · simpa using hsecondRateUniform)
    filter_upwards [hsum] with n hn
    simpa using hn
  have hpowN : ∀ᶠ n : ℕ in atTop, (N n : ℝ) = Real.exp (L n) := by
    filter_upwards [hLpos] with n hn
    have hnNat : 0 < N n := by
      by_contra h
      have hz : N n = 0 := Nat.eq_zero_of_not_pos h
      simp [L, hz] at hn
    have hnReal : 0 < (N n : ℝ) := by exact_mod_cast hnNat
    simpa [L] using (Real.exp_log hnReal).symm
  refine ⟨epsilon, hepsilon, ?_⟩
  filter_upwards [hraw, horder, hm, hsumExp, hLpos, hpowN]
    with n hrawn hord hmn hsumExpx hLn hpowNn
  have hNpos : 0 < (N n : ℝ) := by
    have hnNat : 0 < N n := by
      by_contra h
      have hz : N n = 0 := Nat.eq_zero_of_not_pos h
      simp [L, hz] at hLn
    exact_mod_cast hnNat
  have hmENN : (m n : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (a * L n)) := by
    calc
      (m n : ℝ≥0∞) = ENNReal.ofReal (m n : ℝ) :=
        (ENNReal.ofReal_natCast (m n)).symm
      _ ≤ ENNReal.ofReal ((N n : ℝ) ^ a) := ENNReal.ofReal_le_ofReal hmn
      _ = ENNReal.ofReal (Real.exp (a * L n)) := by
        rw [Real.rpow_def_of_pos hNpos]
        simp [L, mul_comm]
  have hfirstCount : ((ell n + 1 : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (Real.log ((ellN n : ℝ) + 1))) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_log (by positivity : 0 < (ellN n : ℝ) + 1)]
    exact_mod_cast Nat.add_le_add_right hord 1
  have hspanCount : (D n : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (Real.log ((D n : ℝ) + 1))) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_log (by positivity : 0 < (D n : ℝ) + 1)]
    exact_mod_cast Nat.le_add_right (D n) 1
  have hfirstNum : (m n : ℝ≥0∞) * ((ell n + 1 : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp
        (a * L n + Real.log ((ellN n : ℝ) + 1))) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          ((ell n + 1 : ℕ) : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_right hmENN (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          ENNReal.ofReal (Real.exp (Real.log ((ellN n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hfirstCount (by positivity)
      _ = ENNReal.ofReal (Real.exp
          (a * L n + Real.log ((ellN n : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        rw [← Real.exp_add]
  have hsecondNum : (m n : ℝ≥0∞) *
        ((D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) ≤
      ENNReal.ofReal (Real.exp
        (a * L n + Real.log ((D n : ℝ) + 1) + E n)) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          ((D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) :=
        mul_le_mul_of_nonneg_right hmENN (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          (ENNReal.ofReal (Real.exp (Real.log ((D n : ℝ) + 1))) *
            ENNReal.ofReal (Real.exp (E n))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hspanCount (by positivity)) (by positivity)
      _ = ENNReal.ofReal (Real.exp
          (a * L n + Real.log ((D n : ℝ) + 1) + E n)) := by
        calc
          _ = ENNReal.ofReal (Real.exp (a * L n) *
              (Real.exp (Real.log ((D n : ℝ) + 1)) * Real.exp (E n))) := by
                rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
                  ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          _ = _ := by
                rw [← Real.exp_add, ← Real.exp_add]
                ring_nf
  have hsumENN : ENNReal.ofReal
      (Real.exp (a * L n + Real.log ((ellN n : ℝ) + 1))) +
        ENNReal.ofReal
          (Real.exp (a * L n + Real.log ((D n : ℝ) + 1) + E n)) ≤
      ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) := by
    rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hsumExpx
  have hnumerator : (m n : ℝ≥0∞) *
      (((ell n + 1 : ℕ) : ℝ≥0∞) +
        (D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) ≤
      ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) := by
    calc
      _ = (m n : ℝ≥0∞) * ((ell n + 1 : ℕ) : ℝ≥0∞) +
          (m n : ℝ≥0∞) * ((D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) := by
            rw [mul_add]
      _ ≤ ENNReal.ofReal
            (Real.exp (a * L n + Real.log ((ellN n : ℝ) + 1))) +
          ENNReal.ofReal
            (Real.exp (a * L n + Real.log ((D n : ℝ) + 1) + E n)) :=
        add_le_add hfirstNum hsecondNum
      _ ≤ ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) := hsumENN
  have hdenOrder : (N n : ℝ≥0∞) ≤ (N n + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ (N n)
  have hNcastENN : (N n : ℝ≥0∞) = ENNReal.ofReal (Real.exp (L n)) := by
    rw [← ENNReal.ofReal_natCast, hpowNn]
  have htargetN : ENNReal.ofReal (Real.exp (-epsilon * L n)) *
      (N n : ℝ≥0∞) = ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) := by
    rw [hNcastENN, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have htargetDen : ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) ≤
      ENNReal.ofReal (Real.exp (-epsilon * L n)) * (N n + 1 : ℕ) := by
    rw [← htargetN]
    exact mul_le_mul_of_nonneg_left hdenOrder (by positivity)
  have hden0 : ((N n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (N n)
  have hdenTop : ((N n + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hquotient :
      (m n : ℝ≥0∞) *
          (((ell n + 1 : ℕ) : ℝ≥0∞) +
            (D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) /
        (N n + 1 : ℕ) ≤ ENNReal.ofReal (Real.exp (-epsilon * L n)) :=
    (ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdenTop)).2
      (le_trans hnumerator htargetDen)
  calc
    P n ≤ (m n : ℝ≥0∞) *
        (((ell n + 1 : ℕ) : ℝ≥0∞) +
          (D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) /
        (N n + 1 : ℕ) := by simpa [D] using hrawn
    _ ≤ ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
      simpa [L] using hquotient

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
