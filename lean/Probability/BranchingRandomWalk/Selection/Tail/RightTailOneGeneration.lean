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

/-- Paley--Zygmund for an ENNReal-valued nonnegative observable, in the
support-event form used for the number of corridor paths. -/
theorem measure_ne_zero_ge_lintegral_sq_div_lintegral_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ≥0∞) (hX : Measurable X)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, X ω ∂μ) = mean)
    (hsecond : (∫⁻ ω, X ω ^ 2 ∂μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    mean ^ 2 / second ≤ μ {ω | X ω ≠ 0} := by
  let A : Set Ω := {ω | X ω ≠ 0}
  let indicator : Ω → ℝ≥0∞ := A.indicator fun _ => 1
  have hA : MeasurableSet A := by
    change MeasurableSet (X ⁻¹' ({0}ᶜ))
    exact (measurableSet_singleton 0).compl.preimage hX
  have hindicator : Measurable indicator := measurable_const.indicator hA
  have h22 : (2 : ℝ).HolderConjugate 2 := by
    convert Real.HolderConjugate.conjExponent
      (show 1 < (2 : ℝ) by norm_num) using 1 <;>
      norm_num [Real.conjExponent]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ h22
    hindicator.aemeasurable hX.aemeasurable
  have hindicator_sq : (fun ω => indicator ω ^ (2 : ℝ)) = indicator := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [indicator, hω]
  have hindicator_integral :
      (∫⁻ ω, indicator ω ^ (2 : ℝ) ∂μ) = μ A := by
    rw [hindicator_sq]
    exact lintegral_indicator_one hA
  have hX_on_A : ∀ ω, indicator ω * X ω = X ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [indicator, hω]
    · have hzero : X ω = 0 := by
        by_contra hne
        exact hω hne
      simp [indicator, hω, hzero]
  have hHolder' :
      mean ≤ (μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ) := by
    calc
      mean = ∫⁻ ω, indicator ω * X ω ∂μ := by
        rw [lintegral_congr fun ω => hX_on_A ω, hmean]
      _ ≤ (∫⁻ ω, indicator ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, X ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hHolder
      _ ≤ (μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ) := by
        rw [hindicator_integral]
        gcongr
        simpa [pow_two] using hsecond
  have hroot (x : ℝ≥0∞) :
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) =
          (x ^ (1 / 2 : ℝ)) ^ 2 := by rw [pow_two]
      _ = x ^ ((1 / 2 : ℝ) * (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        congr 1
      _ = x := by
        have hhalf : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
        rw [hhalf, ENNReal.rpow_one]
  have hsq : mean ^ 2 ≤ μ A * second := by
    have hmul := mul_le_mul hHolder' hHolder' (by positivity) (by positivity)
    calc
      mean ^ 2 = mean * mean := by rw [pow_two]
      _ ≤ ((μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) ^ 2 := by
        simpa [pow_two] using hmul
      _ = μ A * second := by
        rw [pow_two]
        calc
          ((μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) *
              ((μ A) ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) =
            ((μ A) ^ (1 / 2 : ℝ) * (μ A) ^ (1 / 2 : ℝ)) *
              (second ^ (1 / 2 : ℝ) * second ^ (1 / 2 : ℝ)) := by ac_rfl
          _ = μ A * second := by rw [hroot, hroot]
  apply (ENNReal.div_le_iff_le_mul
    (Or.inl hsecond_pos.ne') (Or.inl hsecond_top)).2
  simpa [mul_comm] using hsq

/-- A corridor contains a surviving generation-`n` path exactly when the
unweighted corridor path count is nonzero. -/
theorem pathGeneration_ne_zero_iff_hasPathHistoryIn
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (initial : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (ω : StepField ℕ X) :
    Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ≠ 0 ↔
      ω ∈ hasPathHistoryIn (ι := ℕ) φ n initial corridor := by
  classical
  constructor
  · intro hcount
    by_contra hpath
    have hterms (u : TreeNode ℕ) :
        Spine.pathGenerationTerm φ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω = 0 := by
      by_cases hu : u.length = n
      · by_cases hs : surviveAlong ω [] u
        · have hnot : Spine.pathHistory φ n initial ω u ∉ corridor := by
            intro hmem
            exact hpath ⟨u, hu, hs, hmem⟩
          simp [Spine.pathGenerationTerm, Set.indicator, hu, hs, hnot]
        · simp [Spine.pathGenerationTerm, hu, hs]
      · simp [Spine.pathGenerationTerm, hu]
    have hzero : Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω = 0 := by
      unfold Spine.pathGeneration
      rw [ENNReal.tsum_eq_zero]
      exact hterms
    exact hcount hzero
  · rintro ⟨u, hu, hs, hcorridor⟩
    have hterm : Spine.pathGenerationTerm φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω = 1 := by
      simp [Spine.pathGenerationTerm, Set.indicator, hu, hs, hcorridor]
    have hle : 1 ≤ Spine.pathGeneration φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω := by
      unfold Spine.pathGeneration
      calc
        1 = Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial u ω := hterm.symm
        _ ≤ ∑' p : TreeNode ℕ, Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial p ω :=
          ENNReal.le_tsum (f := fun p => Spine.pathGenerationTerm φ n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial p ω) u
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle)

/-- Paley--Zygmund converts first and second moment estimates for the
generation-`n` corridor path count into a lower bound on one-root tube
success. This is the probability step used in the paper's long-corridor
estimate. -/
theorem measure_hasPathHistoryIn_ge_of_pathGeneration_moments
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (mean second : ℝ≥0∞)
    (hmean : (∫⁻ ω, Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂stepFieldLaw μ) = mean)
    (hsecond : (∫⁻ ω, (Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω) ^ 2
      ∂stepFieldLaw μ) ≤ second)
    (hsecond_pos : 0 < second) (hsecond_top : second ≠ ∞) :
    mean ^ 2 / second ≤
      (stepFieldLaw μ) (hasPathHistoryIn (ι := ℕ) φ n initial corridor) := by
  let Xcount : StepField ℕ X → ℝ≥0∞ := fun ω =>
    Spine.pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
  have hX : Measurable Xcount := Spine.pathGeneration_measurable φ n
    (measurable_const.indicator hcorridor) initial
  have hPZ := measure_ne_zero_ge_lintegral_sq_div_lintegral_sq
    (stepFieldLaw μ) Xcount hX mean second hmean hsecond
    hsecond_pos hsecond_top
  have hsupport : {ω : StepField ℕ X | Xcount ω ≠ 0} =
      hasPathHistoryIn (ι := ℕ) φ n initial corridor := by
    ext ω
    exact pathGeneration_ne_zero_iff_hasPathHistoryIn
      φ n initial corridor ω
  simpa [Xcount, hsupport] using hPZ

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

/-- The independent initial roots all miss a measurable one-root event with
probability equal to the one-root failure probability raised to the number of
roots.  The event may inspect the entire pre-sampled descendant field of a
root, so this is the independence interface needed for multi-generation tube
success events as well as one-generation hits. -/
theorem measure_allRootsAvoidStepFieldEvent_eq_pow
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} =
      ((stepFieldLaw μ) Eᶜ) ^ m := by
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
        {field : FiniteRootStepField m ℕ X | ∀ r : Fin m, field r ∉ E} := by
    ext field
    simp
  rw [hset] at hfactor
  have hprod :
      (∏ r ∈ Finset.univ,
        (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ)) =
        ((stepFieldLaw μ) Eᶜ) ^ m := by
    simp_rw [hroot]
    simp
  rw [hprod] at hfactor
  exact hfactor

/-- If one initial root has probability at least `p` of a measurable event
in its whole descendant field, then the chance that all `m` independent
roots miss the event is at most `exp (-m * p)`. -/
theorem measure_allRootsAvoidStepFieldEvent_le_exp
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hprob : p ≤ ((stepFieldLaw μ) E).toReal) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
  let q : ℝ≥0∞ := (stepFieldLaw μ) E
  have hqtop : q ≠ ∞ := measure_ne_top _ _
  have hpq : ENNReal.ofReal p ≤ q := by
    calc
      ENNReal.ofReal p ≤ ENNReal.ofReal q.toReal :=
        ENNReal.ofReal_le_ofReal hprob
      _ = q := ENNReal.ofReal_toReal hqtop
  have hfailure :
      (stepFieldLaw μ) Eᶜ ≤ 1 - ENNReal.ofReal p := by
    have hcompl := prob_compl_le_one_sub_of_le_prob
      (μ := stepFieldLaw μ) (p := ENNReal.ofReal p) (s := E)
      (by simpa [q] using hpq) hE
    exact hcompl
  have hbase :
      1 - ENNReal.ofReal p = ENNReal.ofReal (1 - p) := by
    simpa using (ENNReal.ofReal_sub 1 hp).symm
  have hexp : (1 - p) ^ m ≤ Real.exp (-(m : ℝ) * p) := by
    calc
      (1 - p) ^ m ≤ (Real.exp (-p)) ^ m :=
        pow_le_pow_left₀ (sub_nonneg.mpr hp_one) (Real.one_sub_le_exp_neg p) m
      _ = Real.exp (-(m : ℝ) * p) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hpow :
      (ENNReal.ofReal (1 - p)) ^ m ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
    calc
      (ENNReal.ofReal (1 - p)) ^ m = ENNReal.ofReal ((1 - p) ^ m) :=
        (ENNReal.ofReal_pow (sub_nonneg.mpr hp_one) m).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) :=
        ENNReal.ofReal_le_ofReal hexp
  calc
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} =
      ((stepFieldLaw μ) Eᶜ) ^ m :=
        measure_allRootsAvoidStepFieldEvent_eq_pow μ E hE m
    _ ≤ (1 - ENNReal.ofReal p) ^ m :=
      pow_le_pow_left₀ (by positivity) hfailure m
    _ = (ENNReal.ofReal (1 - p)) ^ m := by rw [hbase]
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := hpow

/-- Exponential extinction bound for independent roots when success means
that the root's branching field contains a surviving generation-`n` path in
a prescribed measurable history corridor. -/
theorem measure_allRootsAvoidPathHistoryIn_le_exp
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (initial : ℝ) (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor) (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hprob : p ≤ ((stepFieldLaw μ)
      (hasPathHistoryIn (ι := ℕ) φ n initial corridor)).toReal) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m,
            field r ∉ hasPathHistoryIn (ι := ℕ) φ n initial corridor} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
  exact measure_allRootsAvoidStepFieldEvent_le_exp μ _
    (measurableSet_hasPathHistoryIn φ n initial corridor hcorridor)
    m p hp hp_one hprob

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
