/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.Basic
public import Mathlib.Probability.Independence.Process.Basic

/-!
# Splitting an independent increment field at its first coordinate

These results expose the product decomposition used by the path form of the
many-to-one formula.  They are stated for an arbitrary real increment law.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching.Walk

theorem infinitePi_head_indep_incrementTail (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    IndepFun (fun increment : ℕ → ℝ => increment 0) incrementTail
      (Measure.infinitePi fun _ : ℕ => ν) := by
  let P : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  have hind : iIndepFun (fun k (increment : ℕ → ℝ) => increment k) P :=
    iIndepFun_infinitePi (X := fun _ : ℕ => id) (fun _ => measurable_id)
  apply IndepFun.indepFun_process
      (measurable_pi_apply 0) (fun k => measurable_pi_apply (k + 1))
  intro I
  have hfinite := iIndepFun.indepFun_finset ({0} : Finset ℕ)
    (I.image Nat.succ) (by simp) hind (fun k => measurable_pi_apply k)
  let left : ({k : ℕ // k ∈ ({0} : Finset ℕ)} → ℝ) → ℝ :=
    fun z => z ⟨0, by simp⟩
  let right : ({k : ℕ // k ∈ I.image Nat.succ} → ℝ) → (I → ℝ) :=
    fun z k => z ⟨k.1 + 1, by
      simp only [Finset.mem_image]
      exact ⟨k.1, k.2, rfl⟩⟩
  have h := hfinite.comp
    (show Measurable left by fun_prop)
    (show Measurable right by fun_prop)
  simpa [left, right, Function.comp_def] using h

theorem infinitePi_incrementTail_law (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : ℕ => ν).map incrementTail =
      Measure.infinitePi fun _ : ℕ => ν := by
  change (Measure.infinitePi fun _ : ℕ => ν).map
      (fun increment k => increment (Nat.succ k)) = _
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => ν) Nat.succ_injective

theorem infinitePi_head_incrementTail_law (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : ℕ => ν).map
        (fun increment => (increment 0, incrementTail increment)) =
      ν.prod (Measure.infinitePi fun _ : ℕ => ν) := by
  rw [(infinitePi_head_indep_incrementTail ν).map_prod_eq_prod_map_map
      (measurable_pi_apply 0).aemeasurable incrementTail_measurable.aemeasurable,
    Measure.infinitePi_map_eval, infinitePi_incrementTail_law]

/-- Integrating a path of length `n + 1` is the iterated integral over its
first increment and an independent tail increment field. -/
theorem lintegral_history_succ (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) (x : ℝ)
    {F : (Fin (n + 2) → ℝ) → ENNReal} (hF : Measurable F) :
    (∫⁻ increment, F (history (n + 1) x increment)
        ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ∫⁻ y, ∫⁻ tail,
        F (prependHistory x (history n (x + y) tail))
        ∂Measure.infinitePi (fun _ : ℕ => ν) ∂ν := by
  let P : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  let H : ℝ × (ℕ → ℝ) → ENNReal := fun z =>
    F (prependHistory x (history n (x + z.1) z.2))
  have hspine : Measurable (fun z : ℝ × (ℕ → ℝ) =>
      history n (x + z.1) z.2) :=
    (history_joint_measurable n).comp
      ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hH : Measurable H := by
    apply hF.comp
    exact (prependHistory_joint_measurable n).comp
      (measurable_const.prodMk hspine)
  have hsplit : Measurable (fun increment : ℕ → ℝ =>
      (increment 0, incrementTail increment)) :=
    (measurable_pi_apply 0).prodMk incrementTail_measurable
  calc
    (∫⁻ increment, F (history (n + 1) x increment) ∂P) =
        ∫⁻ increment, H (increment 0, incrementTail increment) ∂P := by
      apply lintegral_congr
      intro increment
      rw [history_succ]
    _ = ∫⁻ z, H z ∂P.map
          (fun increment => (increment 0, incrementTail increment)) := by
      exact (lintegral_map hH hsplit).symm
    _ = ∫⁻ z, H z ∂ν.prod P := by
      rw [infinitePi_head_incrementTail_law]
    _ = ∫⁻ y, ∫⁻ tail, H (y, tail) ∂P ∂ν :=
      lintegral_prod H hH.aemeasurable
    _ = _ := rfl

/-- The same first-step decomposition with the reciprocal exponential weight
accumulated along the complete path. -/
theorem lintegral_history_succ_withWeight (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) (x : ℝ)
    {F : (Fin (n + 2) → ℝ) → ENNReal} (hF : Measurable F) :
    (∫⁻ increment,
        ENNReal.ofReal (Real.exp (partialSum (n + 1) increment)) *
          F (history (n + 1) x increment)
        ∂Measure.infinitePi (fun _ : ℕ => ν)) =
      ∫⁻ y, ENNReal.ofReal (Real.exp y) *
        ∫⁻ tail, ENNReal.ofReal (Real.exp (partialSum n tail)) *
          F (prependHistory x (history n (x + y) tail))
          ∂Measure.infinitePi (fun _ : ℕ => ν) ∂ν := by
  let P : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => ν
  let H : ℝ × (ℕ → ℝ) → ENNReal := fun z =>
    ENNReal.ofReal (Real.exp (z.1 + partialSum n z.2)) *
      F (prependHistory x (history n (x + z.1) z.2))
  have hH : Measurable H := by
    have hspine : Measurable (fun z : ℝ × (ℕ → ℝ) =>
        history n (x + z.1) z.2) :=
      (history_joint_measurable n).comp
        ((measurable_const.add measurable_fst).prodMk measurable_snd)
    exact ((measurable_fst.add
      ((partialSum_measurable n).comp measurable_snd)).exp.ennreal_ofReal).mul
        (hF.comp ((prependHistory_joint_measurable n).comp
          (measurable_const.prodMk hspine)))
  have hsplit : Measurable (fun increment : ℕ → ℝ =>
      (increment 0, incrementTail increment)) :=
    (measurable_pi_apply 0).prodMk incrementTail_measurable
  calc
    (∫⁻ increment,
        ENNReal.ofReal (Real.exp (partialSum (n + 1) increment)) *
          F (history (n + 1) x increment) ∂P) =
        ∫⁻ increment, H (increment 0, incrementTail increment) ∂P := by
      apply lintegral_congr
      intro increment
      rw [history_succ, partialSum_succ_eq_head_add_tail]
    _ = ∫⁻ z, H z ∂P.map
          (fun increment => (increment 0, incrementTail increment)) := by
      exact (lintegral_map hH hsplit).symm
    _ = ∫⁻ z, H z ∂ν.prod P := by
      rw [infinitePi_head_incrementTail_law]
    _ = ∫⁻ y, ∫⁻ tail, H (y, tail) ∂P ∂ν :=
      lintegral_prod H hH.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (Real.exp y) *
          ∫⁻ tail, ENNReal.ofReal (Real.exp (partialSum n tail)) *
            F (prependHistory x (history n (x + y) tail)) ∂P ∂ν := by
      apply lintegral_congr
      intro y
      have hinner : Measurable (fun tail : ℕ → ℝ =>
          ENNReal.ofReal (Real.exp (partialSum n tail)) *
            F (prependHistory x (history n (x + y) tail))) :=
        (partialSum_measurable n).exp.ennreal_ofReal.mul
          (hF.comp ((prependHistory_joint_measurable n).comp
            (measurable_const.prodMk (history_measurable n (x + y)))))
      rw [← lintegral_const_mul (ENNReal.ofReal (Real.exp y)) hinner]
      apply lintegral_congr
      intro tail
      simp only [H]
      rw [Real.exp_add,
        ENNReal.ofReal_mul (le_of_lt (Real.exp_pos y)), mul_assoc]

end ProbabilityTheory.BranchingRandomWalk.Spine
