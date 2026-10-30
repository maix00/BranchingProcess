/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Basic
public import Topology.Cadlag.Skorokhod.Topology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Topology.Cadlag.Measurability
import Topology.Cadlag.Skorokhod.Path.Endpoint
import Topology.Cadlag.Skorokhod.Evaluation.Integral

/-!
# Measurable evaluation on Skorokhod path space

Evaluation at a fixed time is Borel measurable for càdlàg paths with values in
any metrizable Borel state space. The proof first establishes measurability
after composition with bounded continuous real-valued probes. For a closed
set, it uses the arctangent of distance to that set; right-interval averages
recover the probe value at the selected time.

## Public declarations

- `measurable_apply t`: the evaluation map `path ↦ path t` is Borel measurable
  on the `J₁` path space.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Skorokhod

private lemma norm_arctan_le_pi (x : ℝ) : ‖Real.arctan x‖ ≤ Real.pi := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := Real.arctan_lt_pi_div_two (-x)
    rw [Real.arctan_neg] at h
    linarith [Real.pi_pos]
  · exact (Real.arctan_lt_pi_div_two x).le.trans (by linarith [Real.pi_pos])

private theorem measurable_continuous_comp_apply
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (g : E → ℝ) (hg : Continuous g) (bound : ℝ)
    (hbound : ∀ x, ‖g x‖ ≤ bound) (t : unitInterval) :
    Measurable (fun path : CadlagPath unitInterval E => g (path t)) := by
  by_cases ht : t = ⊤
  · subst t
    exact (hg.comp continuous_apply_top).measurable
  have ht' : (t : ℝ) < 1 := by
    have hne : t ≠ ⊤ := ht
    exact (lt_top_iff_ne_top).2 hne
  let d : ℕ → ℝ := fun n => (1 - (t : ℝ)) * ((n : ℝ) + 1)⁻¹
  have hdpos (n : ℕ) : 0 < d n := by
    dsimp [d]
    exact mul_pos (sub_pos.mpr ht') (inv_pos.mpr (by positivity))
  have hdnonneg (n : ℕ) : 0 ≤ d n := (hdpos n).le
  have hdle (n : ℕ) : d n ≤ 1 - (t : ℝ) := by
    dsimp [d]
    have hn : (1 : ℕ) ≤ n + 1 := by omega
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hn
    have hdenpos : 0 < (n : ℝ) + 1 := by positivity
    exact mul_le_of_le_one_right (sub_nonneg.mpr (t.property.2))
      ((inv_le_one₀ hdenpos).2 hden)
  let ψ : ℕ → ℝ → unitInterval := fun n u =>
    ⟨(t : ℝ) + d n * (Set.projIcc 0 1 zero_le_one u : ℝ), by
      constructor
      · exact add_nonneg t.property.1
          (mul_nonneg (hdnonneg n) (Set.projIcc 0 1 zero_le_one u).property.1)
      · calc
          (t : ℝ) + d n * (Set.projIcc 0 1 zero_le_one u : ℝ) ≤
              (t : ℝ) + d n :=
                calc
                  _ = d n * (Set.projIcc 0 1 zero_le_one u : ℝ) + t := by ring
                  _ ≤ d n + t := add_le_add_left
                    (mul_le_of_le_one_right (hdnonneg n)
                      (Set.projIcc 0 1 zero_le_one u).property.2) t
                  _ = t + d n := by ring
          _ ≤ 1 := by linarith [hdle n, t.property.2]⟩
  have hψ_cont (n : ℕ) : Continuous (ψ n) := by
    apply Continuous.subtype_mk
    fun_prop
  have hψ_inj (n : ℕ) : Set.InjOn (ψ n) (Icc 0 1) := by
    intro u hu v hv huv
    have hprojU : (Set.projIcc 0 1 zero_le_one u : ℝ) = u := by
      simpa using congrArg (fun x : unitInterval => (x : ℝ))
        (Set.projIcc_of_mem zero_le_one hu)
    have hprojV : (Set.projIcc 0 1 zero_le_one v : ℝ) = v := by
      simpa using congrArg (fun x : unitInterval => (x : ℝ))
        (Set.projIcc_of_mem zero_le_one hv)
    have hval := congrArg (fun x : unitInterval => (x : ℝ)) huv
    have hmul : d n * u = d n * v := by
      simpa [ψ, hprojU, hprojV] using hval
    exact mul_left_cancel₀ (ne_of_gt (hdpos n)) hmul
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hn : ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (Ici_mem_atTop b)
    filter_upwards [hn] with n hn
    exact hn.trans (by norm_num)
  have hd_tendsto : Tendsto d atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    dsimp [d]
    simpa using (tendsto_const_nhds.mul hinv)
  have hpointwise (path : CadlagPath unitInterval E) (u : ℝ)
      (hu : u ∈ Icc 0 1) :
      Tendsto (fun n => g (path (ψ n u))) atTop (𝓝 (g (path t))) := by
    by_cases hu0 : u = 0
    · subst u
      have hzero (n : ℕ) : ψ n 0 = t := by
        apply Subtype.ext
        simp [ψ]
      simp [hzero]
    · have hu_pos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have htime_real : Tendsto (fun n => (ψ n u : ℝ)) atTop (𝓝 (t : ℝ)) := by
        have hconst : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (𝓝 (t : ℝ)) :=
          tendsto_const_nhds
        have huconst : Tendsto (fun _ : ℕ => u) atTop (𝓝 u) := tendsto_const_nhds
        have h := hconst.add (hd_tendsto.mul huconst)
        have heq : (fun n => (ψ n u : ℝ)) = fun n => (t : ℝ) + d n * u := by
          funext n
          change (t : ℝ) + d n * (Set.projIcc 0 1 zero_le_one u : ℝ) = _
          rw [Set.projIcc_of_mem zero_le_one hu]
        rw [heq]
        simpa using h
      have htime : Tendsto (fun n => ψ n u) atTop (𝓝 t) :=
        tendsto_subtype_rng.2 htime_real
      have hgt (n : ℕ) : t < ψ n u := by
        change (t : ℝ) < (ψ n u : ℝ)
        change (t : ℝ) < (t : ℝ) + d n *
          (Set.projIcc 0 1 zero_le_one u : ℝ)
        rw [Set.projIcc_of_mem zero_le_one hu]
        exact lt_add_of_pos_right _ (mul_pos (hdpos n) hu_pos)
      have htimeWithin : Tendsto (fun n => ψ n u) atTop (𝓝[Set.Ioi t] t) :=
        tendsto_nhdsWithin_iff.2
          ⟨htime, Filter.Eventually.of_forall hgt⟩
      exact hg.continuousAt.tendsto.comp
        ((path.isCadlag_toFun.isRightContinuous t).tendsto.comp htimeWithin)
  have hlimit (path : CadlagPath unitInterval E) :
      Tendsto (fun n => integralAlongTimeChange g (ψ n) path)
        atTop (𝓝 (g (path t))) := by
    have hF_meas (n : ℕ) : AEStronglyMeasurable
        (fun u : ℝ => g (path (ψ n u)))
        (volume.restrict (Icc 0 1)) := by
      apply (hg.measurable.comp
        ((path.isCadlag_toFun.measurable).comp (hψ_cont n).measurable)).aestronglyMeasurable
    have h_bound (n : ℕ) : ∀ᵐ u ∂(volume.restrict (Icc 0 1)),
        ‖g (path (ψ n u))‖ ≤ bound :=
      Filter.Eventually.of_forall fun u => hbound _
    have hlim : ∀ᵐ u ∂(volume.restrict (Icc 0 1)),
        Tendsto (fun n => g (path (ψ n u))) atTop (𝓝 (g (path t))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact hpointwise path u hu
    have hdc := tendsto_integral_of_dominated_convergence
      (bound := fun _ : ℝ => bound)
      (F_measurable := hF_meas)
      (bound_integrable := integrable_const bound)
      (h_bound := h_bound)
      (h_lim := hlim)
    simpa [integralAlongTimeChange] using hdc
  let averages : ℕ → CadlagPath unitInterval E → ℝ := fun n path =>
    integralAlongTimeChange g (ψ n) path
  have havg_cont (n : ℕ) : Continuous (averages n) :=
    continuous_iff_continuousAt.mpr fun path => by
      exact continuousAt_integralAlongTimeChange g hg bound hbound
        (ψ n) (hψ_cont n) (hψ_inj n) path
  have havg_limit : Tendsto averages atTop
      (𝓝 fun path : CadlagPath unitInterval E => g (path t)) := by
    rw [tendsto_pi_nhds]
    intro path
    exact hlimit path
  exact measurable_of_tendsto_metrizable
    (fun n => (havg_cont n).measurable) havg_limit

/-- Evaluation at a fixed time is Borel measurable for càdlàg paths with
values in a metrizable Borel state space. The proof first establishes
measurability after composition with every bounded continuous real-valued
probe. For a closed set, the probe is the arctangent of distance to that set;
right-interval averages recover its value at the selected time. -/
theorem measurable_apply {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (t : unitInterval) :
    Measurable (fun path : CadlagPath unitInterval E => path t) := by
  apply measurable_of_isClosed'
  intro s hs hsne _hsuniv
  let probe : E → ℝ := fun x => Real.arctan (Metric.infDist x s)
  have hprobe_cont : Continuous probe :=
    Real.continuous_arctan.comp (Metric.continuous_infDist_pt s)
  have hprobe_bound : ∀ x, ‖probe x‖ ≤ Real.pi := by
    intro x
    exact norm_arctan_le_pi _
  have hprobe := measurable_continuous_comp_apply probe hprobe_cont
    Real.pi hprobe_bound t
  have heq : (fun path : CadlagPath unitInterval E => path t) ⁻¹' s =
      (fun path => probe (path t)) ⁻¹' {0} := by
    ext path
    change path t ∈ s ↔ Real.arctan (Metric.infDist (path t) s) = 0
    rw [hs.mem_iff_infDist_zero hsne]
    exact (Real.arctan_eq_zero_iff).symm
  rw [heq]
  exact (measurableSet_singleton (0 : ℝ)).preimage hprobe

end Skorokhod

end
