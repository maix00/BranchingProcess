/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Probability.Independence.FiniteEventCount

import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Root-indexed event counts and avoidance

In namespace `ProbabilityTheory.BranchingRandomWalk.RootIndexed`, let
`ν₁ := ProbabilityTheory.BranchingProcess.offspringFieldLaw μ`,
`νₘ := finiteRootStepFieldLaw μ m`, and
`N_E(field) := ∑ r : Fin m, 1_E(field r)`.

## Public declarations

For `N_E(F)=\sum_{r\in\operatorname{Fin}(m)}\mathbf 1_E(F(r))`, the
quarter-mean lower-tail bound and the exact avoidance probability are

\[\begin{aligned}
\nu_m\!\left(N_E\le\frac{m\,\operatorname{toReal}(\nu_1(E))}4\right)
&\le\exp\!\left(-\frac{m\,\operatorname{toReal}(\nu_1(E))}4\right),\\
\nu_m\!\left(\forall r,\ F(r)\notin E\right)
&=\bigl(\nu_1(E^{\complement})\bigr)^m.
\end{aligned}\]

* `measure_finiteRootEventCount_le_quarter_mean μ E hE m hm` gives
  `νₘ {field | N_E(field) ≤ m * (ν₁ E).toReal / 4} ≤
  ENNReal.ofReal (exp (-m * (ν₁ E).toReal / 4))` for measurable `E` and
  `0 < m`.
* `measure_finiteRootEventAvoidance_eq_pow μ E hE m` identifies the
  probability that all roots avoid `E` with `(ν₁ Eᶜ)^m`.
* `measure_finiteRootEventAvoidance_le_exp μ E hE m p hp hp_one hprob`
  bounds that probability by `ENNReal.ofReal (exp (-m * p))` when
  `0 ≤ p ≤ 1` and `p ≤ (ν₁ E).toReal`.

The finite iid event-count estimate is provided by the generic theorem
`ProbabilityTheory.measure_iidEventCount_le_quarter_mean`. This file applies
it to independent root fields and proves the exact and exponential
probabilities that all initial roots avoid a measurable one-root event. A
root is counted once when its full pre-sampled branching field belongs to the
specified event.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory

/-- If each independent initial root has probability `q` of a measurable
event in its entire descendant field, then the probability that at most a
quarter of the mean number of roots realize the event is exponentially
small. This is the binomial lower-tail estimate applied after the first tube
stage. -/
theorem measure_finiteRootEventCount_le_quarter_mean
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (_root_.Combinatorics.Branching.StepField ℕ X))
    (hE : MeasurableSet E)
    (m : ℕ) (hm : 0 < m) :
      let q := ((ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) E).toReal
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m, E.indicator (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * q / 4} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * q / 4))) := by
  classical
  let ν := finiteRootStepFieldLaw μ m
  let Xroot : Fin m → FiniteRootStepField m ℕ X →
      _root_.Combinatorics.Branching.StepField ℕ X := fun r field => field r
  let r₀ : Fin m := ⟨0, hm⟩
  have hrootsIndep : iIndepFun Xroot ν := by
    simpa [Xroot, ν] using finiteRootStepFieldLaw_roots_independent μ m
  have hrootsIdent (r : Fin m) : IdentDistrib (Xroot r) (Xroot r₀) ν ν := by
    refine ⟨(measurable_pi_apply r).aemeasurable,
      (measurable_pi_apply r₀).aemeasurable, ?_⟩
    dsimp [ν, Xroot]
    rw [finiteRootStepFieldLaw_root_marginal μ r,
      finiteRootStepFieldLaw_root_marginal μ r₀]
  have hrootprob :
      ν (Xroot r₀ ⁻¹' E) =
        (ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) E := by
    rw [← Measure.map_apply (measurable_pi_apply r₀) hE]
    exact congrArg (fun law : Measure
        (_root_.Combinatorics.Branching.StepField ℕ X) => law E)
      (finiteRootStepFieldLaw_root_marginal μ r₀)
  have hcount := measure_iidEventCount_le_quarter_mean
    ν Xroot Finset.univ r₀ (Finset.mem_univ r₀) E hE
    (fun r => measurable_pi_apply r) hrootsIndep
    (fun r _ => hrootsIdent r)
  simpa [ν, Xroot, hrootprob] using hcount

/-- The independent initial roots all miss a measurable one-root event with
probability equal to the one-root failure probability raised to the number of
roots.  The event may inspect the entire pre-sampled descendant field of a
root, so this is the independence interface needed for multi-generation tube
success events as well as one-generation hits. -/
theorem measure_finiteRootEventAvoidance_eq_pow
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (_root_.Combinatorics.Branching.StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} =
      ((ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) Eᶜ) ^ m := by
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
          ((fun field : FiniteRootStepField m ℕ X => field r) ⁻¹' Eᶜ) =
        (ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) Eᶜ := by
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
        ((ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) Eᶜ) ^ m := by
    simp_rw [hroot]
    simp
  rw [hprod] at hfactor
  exact hfactor

/-- If one initial root has probability at least `p` of a measurable event
in its whole descendant field, then the chance that all `m` independent
roots miss the event is at most `exp (-m * p)`. -/
theorem measure_finiteRootEventAvoidance_le_exp
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (E : Set (_root_.Combinatorics.Branching.StepField ℕ X)) (hE : MeasurableSet E) (m : ℕ)
    (p : ℝ) (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hprob : p ≤ ((ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) E).toReal) :
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          ∀ r : Fin m, field r ∉ E} ≤
      ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := by
  let q : ℝ≥0∞ := (ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) E
  have hqtop : q ≠ ∞ := measure_ne_top _ _
  have hpq : ENNReal.ofReal p ≤ q := by
    calc
      ENNReal.ofReal p ≤ ENNReal.ofReal q.toReal :=
        ENNReal.ofReal_le_ofReal hprob
      _ = q := ENNReal.ofReal_toReal hqtop
  have hfailure :
      (ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) Eᶜ ≤ 1 - ENNReal.ofReal p := by
    have hcompl := prob_compl_le_one_sub_of_le_prob
      (μ := ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) (p := ENNReal.ofReal p) (s := E)
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
      ((ProbabilityTheory.BranchingProcess.offspringFieldLaw μ) Eᶜ) ^ m :=
        measure_finiteRootEventAvoidance_eq_pow μ E hE m
    _ ≤ (1 - ENNReal.ofReal p) ^ m :=
      pow_le_pow_left₀ (by positivity) hfailure m
    _ = (ENNReal.ofReal (1 - p)) ^ m := by rw [hbase]
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * p)) := hpow


end ProbabilityTheory.BranchingRandomWalk.RootIndexed
