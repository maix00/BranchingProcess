/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointL2Sequence
import Probability.MeasureTheory.Convergence.L2FromPolynomialTails

/-!
# Endpoint convergence in `L²`

Combine the endpoint's logarithmic fourth-moment estimate with polynomial
upper and lower deviation bounds on the common countable-root environment.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris

/-- The normalized, centered endpoint minimum on the common countable-root
environment. -/
noncomputable def normalizedCountableRootEndpointMinimum
    (m N H : ℕ) (c : ℝ) : CountableRootStepField ℕ ℝ → ℝ :=
  fun field =>
    @countableRootEndpointMinimum m N H
      (RootIndexed.addressLinearOrder (Fin m) ℕ) field / Real.log (N : ℝ) - c

/-- Polynomial upper and lower deviation bounds for the normalized endpoint,
together with its existing logarithmic fourth-moment estimate, imply
convergence in `L²`. The two tail estimates remain separate inputs so that
the left and right branching-law hypotheses can be supplied independently. -/
theorem normalizedCountableRootEndpointMinimum_tendsto_eLpNorm_two
    {m H : ℕ → ℕ} {t c : ℝ}
    (hm : ∀ n, 1 < n → 0 < m n)
    (hm_le : ∀ n, 1 < n → m n ≤ n)
    (ht : 0 < t)
    (hH : Tendsto
      (fun n => (H n : ℝ) / Real.log (n : ℝ) ^ 3)
      atTop (𝓝 t))
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfour : HasLeftmostFourthMoment L)
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        (RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage).real
          {field | ε ≤ normalizedCountableRootEndpointMinimum
            (m n) n (H n) c field} ≤ C / (n : ℝ) ^ p)
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        (RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage).real
          {field | normalizedCountableRootEndpointMinimum
            (m n) n (H n) c field ≤ -ε} ≤ C / (n : ℝ) ^ p) :
    Tendsto
      (fun n => eLpNorm
        (fun field => if 1 < n then
          normalizedCountableRootEndpointMinimum (m n) n (H n) c field else 0)
        (2 : ℝ≥0∞)
        (RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage))
      atTop (nhds 0) := by
  let μ := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
  let X : ℕ → CountableRootStepField ℕ ℝ → ℝ := fun n field =>
    if 1 < n then normalizedCountableRootEndpointMinimum (m n) n (H n) c field else 0
  let m' : ℕ → ℕ := fun n => if 1 < n then m n else 1
  let N' : ℕ → ℕ := fun n => max n 2
  have hm' : ∀ n, 0 < m' n := by
    intro n
    by_cases hn : 1 < n
    · change 0 < if 1 < n then m n else 1
      simp [hn, hm n hn]
    · change 0 < if 1 < n then m n else 1
      simp [hn]
  have hNlarge' : ∀ n, 1 < N' n := by
    intro n
    dsimp [N']
    exact lt_of_lt_of_le (by norm_num : 1 < 2) (Nat.le_max_right n 2)
  have hm_le' : ∀ n, m' n ≤ N' n := by
    intro n
    by_cases hn : 1 < n
    · have hn2 : 2 ≤ n := by omega
      simpa [m', N', hn, max_eq_left hn2] using hm_le n hn
    · have hsmall : 1 ≤ max n 2 :=
        le_trans (by norm_num : 1 ≤ 2) (Nat.le_max_right n 2)
      simpa [m', N', hn] using hsmall
  have hN' : Tendsto N' atTop atTop := by
    exact tendsto_atTop_mono (fun n => le_max_left n 2) tendsto_id
  have hH' : Tendsto
      (fun n => (H n : ℝ) / Real.log (N' n : ℝ) ^ 3)
      atTop (𝓝 t) := by
    apply hH.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn2 : 2 ≤ n := by omega
    simp [N', max_eq_left hn2]
  have hX : ∀ n, Measurable (X n) := by
    intro n
    by_cases hn : 1 < n
    · letI : LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ) :=
        RootIndexed.addressLinearOrder (Fin (m n)) ℕ
      have hendpoint := measurable_countableRootEndpointMinimum (m n) n (H n)
      simpa [X, hn, normalizedCountableRootEndpointMinimum] using
        (hendpoint.div_const (Real.log (n : ℝ))).sub_const c
    · simpa [X, hn] using
        (measurable_const : Measurable (fun _ : CountableRootStepField ℕ ℝ => (0 : ℝ)))
  have hmoment := countableRootEndpointMinimum_div_sub_fourthMoment_eventually_le_log_eighth
    hm' hNlarge' hm_le' hN' ht hH' L hboundary hnonempty hfour c
  have hX4 : ∀ n, MemLp (X n) (4 : ℝ≥0∞) μ := by
    intro n
    by_cases hn : 1 < n
    · have hn2 : 2 ≤ n := by omega
      have hmEq : m' n = m n := by simp [m', hn]
      have hNEq : N' n = n := by simp [N', max_eq_left hn2]
      have hmem := hmoment.1 n
      rw [hmEq, hNEq] at hmem
      letI : LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ) :=
        RootIndexed.addressLinearOrder (Fin (m n)) ℕ
      have hXEq : X n = normalizedCountableRootEndpointMinimum (m n) n (H n) c := by
        funext field
        simp [X, hn]
      rw [hXEq]
      change MemLp (fun field => countableRootEndpointMinimum (m n) n (H n) field /
        Real.log (n : ℝ) - c) (4 : ℝ≥0∞) μ
      exact hmem
    · simp [X, hn, μ]
  have hfourth : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ field, (X n field) ^ 4 ∂μ) ≤
        C * (1 + Real.log (n : ℝ) ^ 8) := by
    obtain ⟨C, hC, hbound⟩ := hmoment.2
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound, eventually_gt_atTop (1 : ℕ)] with n hboundn hn
    have hn2 : 2 ≤ n := by omega
    have hmEq : m' n = m n := by simp [m', hn]
    have hNEq : N' n = n := by simp [N', max_eq_left hn2]
    have hXEq : X n = normalizedCountableRootEndpointMinimum (m n) n (H n) c := by
      funext field
      simp [X, hn]
    rw [hmEq, hNEq] at hboundn
    rw [hXEq]
    simpa [normalizedCountableRootEndpointMinimum, μ] using hboundn
  have htails : ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧ ∀ᶠ n : ℕ in atTop,
        μ.real ({field | ε ≤ X n field} ∪
          {field | X n field ≤ -ε}) ≤ C / (n : ℝ) ^ p := by
    intro ε hε
    obtain ⟨Cup, pup, hCup, hpup, hup⟩ := hupper ε hε
    obtain ⟨Cdown, pdown, hCdown, hpdown, hdown⟩ := hlower ε hε
    let p := min pup pdown
    have hp : 0 < p := lt_min hpup hpdown
    let C := Cup + Cdown
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨C, p, hC, hp, ?_⟩
    filter_upwards [hup, hdown, eventually_gt_atTop (1 : ℕ)] with n hupn hdownn hn
    have hvalid : 1 < n := by omega
    have hXEq : X n = normalizedCountableRootEndpointMinimum (m n) n (H n) c := by
      funext field
      simp [X, hvalid]
    have hupn' : μ.real {field | ε ≤ X n field} ≤ Cup / (n : ℝ) ^ pup := by
      simpa [μ, hXEq] using hupn
    have hdownn' : μ.real {field | X n field ≤ -ε} ≤ Cdown / (n : ℝ) ^ pdown := by
      simpa [μ, hXEq] using hdownn
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt hn)
    have hpowUp : (n : ℝ) ^ p ≤ (n : ℝ) ^ pup :=
      Real.rpow_le_rpow_of_exponent_le hnreal (min_le_left pup pdown)
    have hpowDown : (n : ℝ) ^ p ≤ (n : ℝ) ^ pdown :=
      Real.rpow_le_rpow_of_exponent_le hnreal (min_le_right pup pdown)
    have hpowPos : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos (by positivity) p
    have hupperCommon : Cup / (n : ℝ) ^ pup ≤ Cup / (n : ℝ) ^ p :=
      div_le_div_of_nonneg_left hCup hpowPos hpowUp
    have hlowerCommon : Cdown / (n : ℝ) ^ pdown ≤ Cdown / (n : ℝ) ^ p :=
      div_le_div_of_nonneg_left hCdown hpowPos hpowDown
    calc
      μ.real ({field | ε ≤ X n field} ∪ {field | X n field ≤ -ε}) ≤
          μ.real {field | ε ≤ X n field} + μ.real {field | X n field ≤ -ε} :=
        measureReal_union_le _ _
      _ ≤ Cup / (n : ℝ) ^ pup + Cdown / (n : ℝ) ^ pdown :=
        add_le_add hupn' hdownn'
      _ ≤ Cup / (n : ℝ) ^ p + Cdown / (n : ℝ) ^ p :=
        add_le_add hupperCommon hlowerCommon
      _ = C / (n : ℝ) ^ p := by
        simp [C, add_div]
  change Tendsto (fun n => eLpNorm (X n) (2 : ℝ≥0∞) μ) atTop (nhds 0)
  exact ProbabilityTheory.tendsto_eLpNorm_two_zero_of_polynomial_tails_log_fourth_moment
    μ X hX hX4 hfourth htails

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
