/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.CountableRootEndpointSublevel
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointL2Convergence

/-!
# Polynomial lower-tail bound for the normalized endpoint

The endpoint sublevel estimate gives the lower polynomial tail required by
the `L²` closure after centering at the trajectory limit. The power exponent
is obtained directly from its exponential-in-logarithm bound.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The paper's logarithmic-scale endpoint sublevel estimate implies the
polynomial lower tail of the normalized endpoint, centered at its limiting
trajectory. The law assumptions are stated individually as in the paper. -/
theorem normalizedCountableRootEndpointMinimum_lowerTail_le_polynomial_of_logarithmic_scales
    {L : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ}
    (hboundary : HasBoundaryNormalization realPotential
      (L : Measure (Step ℕ ℝ)))
    (hnonempty : L.HasAtLeastOneChild)
    (hsupercritical : L.IsSupercritical)
    (hspineMean : (∫ y : ℝ, y ∂tiltedPotentialLaw realPotential (-1)
      (L : Measure (Step ℕ ℝ))) = 0)
    (hspineFiniteVariance : MemLp id 2
      (tiltedPotentialLaw realPotential (-1) (L : Measure (Step ℕ ℝ))))
    {horizon : ℕ → ℕ} {a t : ℝ}
    (ha_zero : 0 ≤ a) (ha_one : a ≤ 1) (ht : 0 < t)
    (hhorizon : Tendsto
      (fun n : ℕ => (horizon n : ℝ) / Real.log (n : ℝ) ^ 3)
      atTop (𝓝 t)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C p : ℝ, 0 ≤ C ∧ 0 < p ∧
        ∀ᶠ n : ℕ in atTop,
          (RootIndexed.stepFieldLaw (Root := ℕ)
            (L : Measure (Step ℕ ℝ))).real
            {field | normalizedCountableRootEndpointMinimum
              (Nat.floor ((n : ℝ) ^ a)) n (horizon n)
              (-a + (Real.pi ^ 2 / 2) *
                (∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
                  (L : Measure (Step ℕ ℝ))) * t) field ≤ -ε} ≤
              C / (n : ℝ) ^ p := by
  intro ε hε
  let variance : ℝ := ∫ y : ℝ, y ^ 2 ∂tiltedPotentialLaw realPotential (-1)
    (L : Measure (Step ℕ ℝ))
  let center : ℝ := -a + (Real.pi ^ 2 / 2) * variance * t
  let μ : Measure (CountableRootStepField ℕ ℝ) :=
    RootIndexed.stepFieldLaw (Root := ℕ) (L : Measure (Step ℕ ℝ))
  let endpoint : ℕ → CountableRootStepField ℕ ℝ → ℝ := fun n field =>
    normalizedCountableRootEndpointMinimum
      (Nat.floor ((n : ℝ) ^ a)) n (horizon n) center field
  obtain ⟨rate, hrate, hsublevel⟩ :=
    eventually_countableRootEndpointMinimum_sublevel_le_polynomial_of_logarithmic_scales
      hboundary hnonempty hsupercritical hspineMean hspineFiniteVariance
      (horizon := horizon) (a := a) (t := t) (zeta := center - ε)
      ha_zero ha_one ht hhorizon (by
        dsimp [center, variance]
        linarith)
  refine ⟨1, rate, by norm_num, hrate, ?_⟩
  filter_upwards [hsublevel, eventually_ge_atTop (2 : ℕ)] with n hsublevel hn
  letI : LinearOrder (RootIndexed.TreeNode
      (Fin (Nat.floor ((n : ℝ) ^ a))) ℕ) :=
    RootIndexed.addressLinearOrder (Fin (Nat.floor ((n : ℝ) ^ a))) ℕ
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hset :
      {field | endpoint n field ≤ -ε} =
        {field | countableRootEndpointMinimum
          (Nat.floor ((n : ℝ) ^ a)) n (horizon n) field ≤
          (center - ε) * Real.log (n : ℝ)} := by
    ext field
    change (countableRootEndpointMinimum
        (Nat.floor ((n : ℝ) ^ a)) n (horizon n) field /
          Real.log (n : ℝ) - center ≤ -ε) ↔
      countableRootEndpointMinimum
        (Nat.floor ((n : ℝ) ^ a)) n (horizon n) field ≤
          (center - ε) * Real.log (n : ℝ)
    constructor
    · intro h
      have hratio :
          countableRootEndpointMinimum
            (Nat.floor ((n : ℝ) ^ a)) n (horizon n) field /
              Real.log (n : ℝ) ≤ center - ε := by
        linarith
      exact (div_le_iff₀ hlog).mp hratio
    · intro h
      have hratio :
          countableRootEndpointMinimum
            (Nat.floor ((n : ℝ) ^ a)) n (horizon n) field /
              Real.log (n : ℝ) ≤ center - ε :=
        (div_le_iff₀ hlog).mpr h
      linarith
  have hboundENN : μ {field | endpoint n field ≤ -ε} ≤
      ENNReal.ofReal (Real.exp (-rate * Real.log (n : ℝ))) := by
    have hsublevel' := hsublevel
    rw [← hset] at hsublevel'
    simpa [μ, endpoint, center, variance] using hsublevel'
  have hboundReal : μ.real {field | endpoint n field ≤ -ε} ≤
      Real.exp (-rate * Real.log (n : ℝ)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hboundENN
    simpa [Measure.real, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  have hrpow : (n : ℝ) ^ rate = Real.exp (rate * Real.log (n : ℝ)) :=
    by
      rw [Real.rpow_def_of_pos hnreal]
      congr 1
      ring
  have hexp : Real.exp (-rate * Real.log (n : ℝ)) =
      1 / (n : ℝ) ^ rate := by
    calc
      Real.exp (-rate * Real.log (n : ℝ)) =
          Real.exp (-(rate * Real.log (n : ℝ))) := by congr 1; ring
      _ = (Real.exp (rate * Real.log (n : ℝ)))⁻¹ := Real.exp_neg _
      _ = ((n : ℝ) ^ rate)⁻¹ := by rw [hrpow]
      _ = 1 / (n : ℝ) ^ rate := by simp
  have hsetTarget :
      {field | endpoint n field ≤ -ε} =
        {field | normalizedCountableRootEndpointMinimum
          (Nat.floor ((n : ℝ) ^ a)) n (horizon n)
          (-a + (Real.pi ^ 2 / 2) * variance * t) field ≤ -ε} := by
    ext field
    rfl
  have hboundPower : μ.real {field | endpoint n field ≤ -ε} ≤
      1 / (n : ℝ) ^ rate := by
    calc
      μ.real {field | endpoint n field ≤ -ε} ≤
          Real.exp (-rate * Real.log (n : ℝ)) := hboundReal
      _ = 1 / (n : ℝ) ^ rate := hexp
  rw [hsetTarget] at hboundPower
  simpa [μ, center, variance] using hboundPower

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
