/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic

import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lower tails for independent root successes

This file supplies the elementary concentration estimate used after the
first tube stage in the positive-initial-mass right-tail argument.  A root is
counted once if its full pre-sampled branching field contains a path in a
specified event.  The root fields are independent, so a Chernoff estimate
controls the lower tail of this count.

For a measurable event `E` of one root field, write
`q = (stepFieldLaw μ)(E)` and
`N_E(field) = ∑ r : Fin m, 1_E(field r)`. The public theorem
`measure_finiteRootEventCount_le_quarter_mean μ E hE m hm` states
`ℙ_{μ^{⊗m}}(N_E ≤ m q / 4) ≤ exp(-m q / 4)` for `0 < m`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory

private lemma mgf_eventIndicator
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) :
    mgf (E.indicator (fun _ => (1 : ℝ))) μ (-1) =
      1 - μ.real E * (1 - Real.exp (-1)) := by
  classical
  have hdecomp :
      (fun ω => Real.exp (-1 * E.indicator (fun _ => (1 : ℝ)) ω)) =
        E.indicator (fun _ => Real.exp (-1)) +
          Eᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  have hleft : Integrable (E.indicator (fun _ => Real.exp (-1))) μ := by
    refine Integrable.of_bound (measurable_const.indicator hE).aestronglyMeasurable
      (Real.exp (-1)) (ae_of_all μ fun ω => ?_)
    by_cases hω : ω ∈ E <;> simp [hω, Real.exp_nonneg]
  have hEcompl : MeasurableSet Eᶜ := MeasurableSet.compl hE
  have hright : Integrable (Eᶜ.indicator (fun _ => (1 : ℝ))) μ := by
    refine Integrable.of_bound (measurable_const.indicator hEcompl).aestronglyMeasurable
      1 (ae_of_all μ fun ω => ?_)
    by_cases hω : ω ∈ E <;> simp [hω]
  calc
    mgf (E.indicator (fun _ => (1 : ℝ))) μ (-1) =
        ∫ ω, Real.exp (-1 * E.indicator (fun _ => (1 : ℝ)) ω) ∂μ := by
          simp [mgf]
    _ = ∫ ω, E.indicator (fun _ => Real.exp (-1)) ω +
          Eᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
            exact integral_congr_ae
              (ae_of_all μ fun ω => congrFun hdecomp ω)
    _ = (∫ ω, E.indicator (fun _ => Real.exp (-1)) ω ∂μ) +
          ∫ ω, Eᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
            exact integral_add' hleft hright
    _ = 1 - μ.real E * (1 - Real.exp (-1)) := by
          rw [integral_indicator_const _ hE,
            integral_indicator_const _ hEcompl,
            smul_eq_mul, smul_eq_mul, measureReal_compl hE, probReal_univ]
          ring

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
      let q := ((ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) E).toReal
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m, E.indicator (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * q / 4} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * q / 4))) := by
  classical
  let ν := finiteRootStepFieldLaw μ m
  let q : ℝ := ((ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) E).toReal
  let Xroot : Fin m → FiniteRootStepField m ℕ X → ℝ := fun r field =>
    E.indicator (fun _ => (1 : ℝ)) (field r)
  let total : FiniteRootStepField m ℕ X → ℝ := fun field =>
    ∑ r : Fin m, Xroot r field
  have hprob :
      (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) E ≤ 1 := by
    calc
      _ ≤ (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) Set.univ :=
        measure_mono (Set.subset_univ E)
      _ = 1 := measure_univ
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact ENNReal.toReal_nonneg
  have hq_le : q ≤ 1 := by
    dsimp [q]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hprob
  have hXroot_meas (r : Fin m) : Measurable (Xroot r) := by
    exact (measurable_const.indicator hE).comp (measurable_pi_apply r)
  have hrootsIndep : iIndepFun Xroot ν := by
    have hfields := finiteRootStepFieldLaw_roots_independent μ m
    let g : _root_.Combinatorics.Branching.StepField ℕ X → ℝ :=
      E.indicator (fun _ => (1 : ℝ))
    have hg : Measurable g := measurable_const.indicator hE
    have hcomp := hfields.comp
      (fun _ : Fin m => g)
      (fun _ => hg)
    simpa [Xroot, g, Function.comp_def, ν] using hcomp
  have hrootsIdent (i j : Fin m) :
      IdentDistrib (Xroot i) (Xroot j) ν ν := by
    have hfields : IdentDistrib
        (fun field : FiniteRootStepField m ℕ X => field i)
        (fun field => field j) ν ν := by
      refine ⟨(measurable_pi_apply i).aemeasurable,
        (measurable_pi_apply j).aemeasurable, ?_⟩
      dsimp [ν]
      rw [finiteRootStepFieldLaw_root_marginal μ i,
        finiteRootStepFieldLaw_root_marginal μ j]
    let g : _root_.Combinatorics.Branching.StepField ℕ X → ℝ :=
      E.indicator (fun _ => (1 : ℝ))
    have hg : Measurable g := measurable_const.indicator hE
    simpa [Xroot, g, Function.comp_def] using hfields.comp hg
  have hbaseIdent : IdentDistrib
      (Xroot (⟨0, hm⟩ : Fin m))
      (fun field : _root_.Combinatorics.Branching.StepField ℕ X =>
        E.indicator (fun _ => (1 : ℝ)) field)
      ν (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) := by
    have hfield : IdentDistrib
        (fun field : FiniteRootStepField m ℕ X => field (⟨0, hm⟩ : Fin m))
        (fun field : _root_.Combinatorics.Branching.StepField ℕ X => field)
        ν (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) := by
      refine ⟨(measurable_pi_apply (⟨0, hm⟩ : Fin m)).aemeasurable,
        measurable_id.aemeasurable, ?_⟩
      dsimp [ν]
      simpa only [Measure.map_id'] using
        finiteRootStepFieldLaw_root_marginal μ (⟨0, hm⟩ : Fin m)
    let g : _root_.Combinatorics.Branching.StepField ℕ X → ℝ :=
      E.indicator (fun _ => (1 : ℝ))
    have hg : Measurable g := measurable_const.indicator hE
    simpa [Xroot, g, Function.comp_def] using hfield.comp hg
  have hsingle : mgf (Xroot (⟨0, hm⟩ : Fin m)) ν (-1) =
      1 - q * (1 - Real.exp (-1)) := by
    calc
      _ = mgf (E.indicator (fun _ => (1 : ℝ)))
          (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) (-1) :=
        (mgf_congr_of_identDistrib
          (Xroot (⟨0, hm⟩ : Fin m))
          (E.indicator (fun _ => (1 : ℝ))) hbaseIdent (-1))
      _ = _ := by
        simpa [q, Measure.real] using mgf_eventIndicator
          (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) E hE
  have hsumMeas : ∀ r, Measurable (Xroot r) := hXroot_meas
  have hsumIntegrable : ∀ r ∈ Finset.univ,
      Integrable (fun ω => Real.exp (-1 * Xroot r ω)) ν := by
    intro r hr
    refine Integrable.of_bound
      (((hXroot_meas r).const_mul (-1)).exp).aestronglyMeasurable 1
      (ae_of_all ν fun field => ?_)
    have hxnonneg : 0 ≤ Xroot r field := by
      by_cases h : field r ∈ E <;> simp [Xroot, h]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hmgfsum : mgf total ν (-1) =
      mgf (Xroot (⟨0, hm⟩ : Fin m)) ν (-1) ^ m := by
    have hsumFun : (∑ r : Fin m, Xroot r) = total := by
      funext field
      simp [total, Finset.sum_apply]
    rw [← hsumFun]
    simpa using mgf_sum_of_identDistrib hsumMeas hrootsIndep
      (fun i _ j _ => hrootsIdent i j)
      (Finset.mem_univ (⟨0, hm⟩ : Fin m)) (-1)
  have hsingle_le : mgf (Xroot (⟨0, hm⟩ : Fin m)) ν (-1) ≤
      Real.exp (-(q / 2)) := by
    rw [hsingle]
    have hexp : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num)
        Real.exp_one_gt_two.le
    calc
      1 - q * (1 - Real.exp (-1)) ≤ 1 - q / 2 := by
        nlinarith [mul_nonneg hq_nonneg (sub_nonneg.mpr hexp)]
      _ ≤ Real.exp (-(q / 2)) := by
        simpa using Real.one_sub_le_exp_neg (q / 2)
  have hmgfsum_le : mgf total ν (-1) ≤ Real.exp (-((m : ℝ) * q / 2)) := by
    rw [hmgfsum]
    calc
      mgf (Xroot (⟨0, hm⟩ : Fin m)) ν (-1) ^ m ≤
          (Real.exp (-(q / 2))) ^ m :=
        pow_le_pow_left₀ (mgf_nonneg) hsingle_le m
      _ = Real.exp (-((m : ℝ) * q / 2)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have htotal_nonneg (field : FiniteRootStepField m ℕ X) : 0 ≤ total field := by
    apply Finset.sum_nonneg
    intro r hr
    have hx : 0 ≤ Xroot r field := by
      by_cases h : field r ∈ E <;> simp [Xroot, h]
    exact hx
  have htotal_meas : Measurable total := by
    dsimp [total]
    exact Finset.measurable_sum _ fun r _ => hXroot_meas r
  have htotalExpIntegrable : Integrable (fun field =>
      Real.exp (-1 * total field)) ν := by
    refine Integrable.of_bound ((htotal_meas.const_mul (-1)).exp).aestronglyMeasurable 1
      (ae_of_all ν fun field => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [htotal_nonneg field]
  have htail := measure_le_le_exp_mul_mgf (X := total) (μ := ν) (t := -1)
    ((m : ℝ) * q / 4) (by norm_num) htotalExpIntegrable
  have htailReal :
      ν.real {field | total field ≤ (m : ℝ) * q / 4} ≤
        Real.exp (-((m : ℝ) * q / 4)) := by
    calc
      _ ≤ Real.exp ((m : ℝ) * q / 4) * mgf total ν (-1) := by
        simpa [mul_comm] using htail
      _ ≤ Real.exp ((m : ℝ) * q / 4) *
          Real.exp (-((m : ℝ) * q / 2)) :=
        mul_le_mul_of_nonneg_left hmgfsum_le (Real.exp_nonneg _)
      _ = Real.exp (-((m : ℝ) * q / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hfinite : (ν {field : FiniteRootStepField m ℕ X |
      total field ≤ (m : ℝ) * q / 4}) ≠ ⊤ :=
    measure_ne_top _ _
  have htailENN : ν {field | total field ≤ (m : ℝ) * q / 4} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) * q / 4))) := by
    calc
      _ = ENNReal.ofReal
          (ν {field | total field ≤ (m : ℝ) * q / 4}).toReal :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ ≤ ENNReal.ofReal (Real.exp (-((m : ℝ) * q / 4))) :=
        ENNReal.ofReal_le_ofReal htailReal
  simpa [ν, q, total, Xroot] using htailENN

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
