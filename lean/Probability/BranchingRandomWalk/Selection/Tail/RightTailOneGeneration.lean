/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.Tail.TwoStageTube
import Probability.BranchingRandomWalk.Selection.Tail.PathManyToOne
import Probability.Distributions.Moments.Signs
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

/-!
# A one-generation upper-tail bound from the offspring law

The cross-child moment assumption gives a quantitative lower bound for a
one-step tube hit. Independent initial roots then give an upper bound for the
probability that no root produces such a child. This is a finite-horizon
consequence of the model assumptions; the longer corridor estimates needed
for (4.15) are separate.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- Quantitative one-step Paley--Zygmund estimate for offspring entering a
bounded-below position window. -/
theorem measure_hasPotentialChildIn_ge_tiltedWindow_sq_div_secondMoment
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (hpositive : 0 < tiltedPotentialLaw φ (-1) μ I) :
    (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ≤
      μ {ξ | hasPotentialChildIn φ I ξ} := by
  let p : ℝ≥0∞ := tiltedPotentialLaw φ (-1) μ I
  let c : ℝ≥0∞ := ∫⁻ ξ, crossChildWeight φ ξ ∂μ
  let d : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-a)) * p + c
  have htilted : IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) :=
    tiltedPotentialLaw_isProbability φ μ hboundary
  have hp : 0 < p := hpositive
  have hp_top : p ≠ ∞ := measure_ne_top (tiltedPotentialLaw φ (-1) μ) I
  have hc_top : c ≠ ∞ := hcross
  have hcoef_pos : 0 < ENNReal.ofReal (Real.exp (-a)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hd_pos : 0 < d := by
    dsimp [d, p, c]
    exact lt_of_lt_of_le
      (ENNReal.mul_pos (ne_of_gt hcoef_pos) (ne_of_gt hpositive))
      (le_add_right le_rfl)
  have hd_top : d ≠ ∞ := by
    dsimp [d, p, c]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top, hc_top⟩
  have hq := tiltedWindowProbability_le_sqrt_success_mul_secondMoment
    φ I a hI hlower μ
  have hroot (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = (x ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [pow_two]
      _ = x ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
      _ = x := by
        have hhalf : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
        rw [hhalf, ENNReal.rpow_one]
  have hmul :
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ) *
        ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ)) =
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
    calc
      _ = ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
            (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ)) *
          (d ^ (1 / 2 : ℝ) * d ^ (1 / 2 : ℝ)) := by ac_rfl
      _ = (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
        rw [hroot, hroot]
  have hsq : p ^ 2 ≤
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := by
    have hsquare := mul_le_mul hq hq (by positivity) (by positivity)
    calc
      p ^ 2 = p * p := by rw [pow_two]
      _ ≤ (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
          d ^ (1 / 2 : ℝ) *
          ((μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
            d ^ (1 / 2 : ℝ)) := by
          simpa [p, d, mul_assoc] using hsquare
      _ = (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) * d := hmul
  have hq : p ^ 2 / d ≤ μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} := by
    apply (ENNReal.div_le_iff_le_mul (Or.inl hd_pos.ne') (Or.inl hd_top)).2
    simpa [mul_comm] using hsq
  have hsuccess :
      μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} =
        μ {ξ | hasPotentialChildIn φ I ξ} := by
    congr 1
    ext ξ
    exact (weightedOffspringWindowMass_ne_zero_iff φ I ξ)
  simpa [p, d, hsuccess] using hq

/-- Under the finite-root product law, the probability that every initial root
fails to produce a child in `I` is the `m`th power of the one-root failure
probability. -/
theorem measure_noRootHasPotentialChildIn_eq_pow
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (hI : MeasurableSet I)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} =
      ((stepFieldLaw μ)
        {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])}) ^ m := by
  let E : Set (StepField ℕ X) :=
    {ω | hasPotentialChildIn φ I (ω [])}
  have hE : MeasurableSet E := by
    exact (measurableSet_hasPotentialChildIn φ I hI).preimage
      (measurable_pi_apply ([] : TreeNode ℕ))
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        (stepFieldLaw μ) Eᶜ := by
    rw [← Measure.map_apply (measurable_pi_apply r) hE.compl]
    rw [finiteRootStepFieldLaw_root_marginal μ r]
  have hfactor :=
    (finiteRootStepFieldLaw_roots_independent μ m).measure_inter_preimage_eq_mul
      Finset.univ (sets := fun _ : Fin m => Eᶜ)
      (by intro r hr; exact hE.compl)
  have hset :
      (⋂ r ∈ Finset.univ,
          (fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} := by
    ext field
    simp [E]
  rw [hset] at hfactor
  have hnot : Eᶜ =
      {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])} := by
    ext ω
    simp [E]
  have hprod :
      (∏ r ∈ Finset.univ,
          (finiteRootStepFieldLaw μ m)
            ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ)) =
        ((stepFieldLaw μ) Eᶜ) ^ m := by
    simp_rw [hroot]
    simp
  rw [hprod] at hfactor
  rw [hnot] at hfactor
  exact hfactor

/-- A one-generation upper bound for all-root failure.  Its one-root success
probability is bounded below from the actual offspring law by the
second-moment estimate. -/
theorem measure_noRootHasPotentialChildIn_le_secondMomentPower
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (hcross : HasFiniteCrossWeight φ μ)
    (hpositive : 0 < tiltedPotentialLaw φ (-1) μ I)
    (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} ≤
      (1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ m := by
  let E : Set (StepField ℕ X) :=
    {ω | hasPotentialChildIn φ I (ω [])}
  let A : Set (Step ℕ X) := {ξ | hasPotentialChildIn φ I ξ}
  have hA : MeasurableSet A := measurableSet_hasPotentialChildIn φ I hI
  have hE : MeasurableSet E := by
    exact hA.preimage (measurable_pi_apply ([] : TreeNode ℕ))
  have hnot : Eᶜ =
      {ω : StepField ℕ X | ¬ hasPotentialChildIn φ I (ω [])} := by
    ext ω
    simp [E]
  have hmap : (stepFieldLaw μ) E = μ A := by
    rw [show E = (fun ω : StepField ℕ X => ω []) ⁻¹' A by rfl]
    rw [← Measure.map_apply (measurable_pi_apply ([] : TreeNode ℕ)) hA]
    rw [stepFieldLaw_coordinate μ []]
  have hhit := measure_hasPotentialChildIn_ge_tiltedWindow_sq_div_secondMoment
    φ I a hI hlower μ hboundary hcross hpositive
  have hprob :
      (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≤ μ A := by
    simpa [A] using hhit
  have hmiss :
      (stepFieldLaw μ) Eᶜ ≤
        1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
          (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
            ∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
    have hmiss' := prob_compl_le_one_sub_of_le_prob
      (μ := stepFieldLaw μ) (p := μ A) (s := E)
      (by rw [hmap]) hE
    exact hmiss'.trans (tsub_le_tsub_left hprob 1)
  have hformula := measure_noRootHasPotentialChildIn_eq_pow φ I hI μ m
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, ¬ hasPotentialChildIn φ I (field r [])} =
      ((stepFieldLaw μ) Eᶜ) ^ m := by
        rw [hformula]
        rw [← hnot]
    _ ≤
      (1 - (tiltedPotentialLaw φ (-1) μ I) ^ 2 /
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          ∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ m :=
      pow_le_pow_left₀ (by positivity) hmiss m

/-- First-moment bound for the number of surviving particles whose complete
ancestral history lies in a measurable corridor. This is the form of the
many-to-one estimate used with Markov's inequality for a killed population. -/
theorem lintegral_pathGeneration_le_exp_mul_spineProbability
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminal : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) ≤
      ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
        (tiltedIncrementFieldLaw φ μ)
          {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor} := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | ProbabilityTheory.RandomWalk.history n initial increment ∈
      corridor}
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hspineEvent : MeasurableSet spineEvent :=
    hcorridor.preimage
      (ProbabilityTheory.RandomWalk.history_measurable n initial)
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hterminalPath (increment : ℕ → ℝ) (hevent : increment ∈ spineEvent) :
      AdditivePath.displacement n increment ≤ terminalUpper - initial := by
    have h := hterminal
      (ProbabilityTheory.RandomWalk.history n initial increment)
      (by simpa [spineEvent] using hevent)
    rw [ProbabilityTheory.RandomWalk.history_last,
      AdditivePath.fromIncrements_apply] at h
    linarith
  calc
    _ = ∫⁻ increment,
          ENNReal.ofReal (Real.exp (AdditivePath.displacement n increment)) *
            F (ProbabilityTheory.RandomWalk.history n initial increment)
          ∂tiltedIncrementFieldLaw φ μ :=
      Spine.pathManyToOneCore φ μ hboundary n hF initial
    _ ≤ ∫⁻ increment,
          ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
          ∂tiltedIncrementFieldLaw φ μ := by
      apply lintegral_mono
      intro increment
      change ENNReal.ofReal
          (Real.exp (AdditivePath.displacement n increment)) *
          F (ProbabilityTheory.RandomWalk.history n initial increment) ≤
        ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
          spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment
      by_cases hevent : increment ∈ spineEvent
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∈
            corridor := by
          simpa [spineEvent] using hevent
        have hexp : ENNReal.ofReal
              (Real.exp (AdditivePath.displacement n increment)) ≤
            ENNReal.ofReal (Real.exp (terminalUpper - initial)) :=
          ENNReal.ofReal_le_ofReal
            (Real.exp_le_exp.mpr (hterminalPath increment hevent))
        have hFval :
            F (ProbabilityTheory.RandomWalk.history n initial increment) = 1 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 1
          rw [Set.indicator_of_mem hhistory]
        have hindicator :
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 1 := by
          simp [Set.indicator, hevent]
        rw [hFval, hindicator]
        simpa using hexp
      · have hhistory : ProbabilityTheory.RandomWalk.history n initial increment ∉
            corridor := by
          intro h
          exact hevent (by simpa [spineEvent] using h)
        have hFzero :
            F (ProbabilityTheory.RandomWalk.history n initial increment) = 0 := by
          change corridor.indicator (fun _ => (1 : ℝ≥0∞))
            (ProbabilityTheory.RandomWalk.history n initial increment) = 0
          rw [Set.indicator_of_notMem hhistory]
        have hindicator :
            spineEvent.indicator (fun _ => (1 : ℝ≥0∞)) increment = 0 := by
          simp [Set.indicator, hevent]
        rw [hFzero, hindicator]
        simp
    _ = ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
        (tiltedIncrementFieldLaw φ μ) spineEvent := by
      rw [lintegral_const_mul _ (measurable_const.indicator hspineEvent)]
      rw [lintegral_indicator_const hspineEvent]
      simp

end ProbabilityTheory.BranchingRandomWalk.Selection.Tail
