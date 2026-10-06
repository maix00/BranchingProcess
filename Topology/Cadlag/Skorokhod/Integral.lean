/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import MeasureTheory.Function.Cadlag
public import Topology.Cadlag.Skorokhod.Endpoint
public import Topology.Cadlag.Skorokhod.Evaluation

/-!
# Integral functionals on Skorokhod path space

Integrating a bounded continuous transform of a càdlàg path along an injective
continuous time parametrization gives a continuous functional for the `J₁`
topology. The proof uses pointwise convergence at the continuity times of the
limit path and dominated convergence.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Skorokhod

private theorem norm_arctan_le_pi (x : ℝ) : ‖Real.arctan x‖ ≤ Real.pi := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := Real.arctan_lt_pi_div_two (-x)
    rw [Real.arctan_neg] at h
    linarith [Real.pi_pos]
  · exact (Real.arctan_lt_pi_div_two x).le.trans (by linarith [Real.pi_pos])

/-- Integrate a continuous state transform of a path along a time
parametrization, using Lebesgue measure on the unit interval. -/
noncomputable def integralAlongTimeChange
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (φ : E → ℝ) (ψ : ℝ → unitInterval) (path : CadlagPath unitInterval E) : ℝ :=
  ∫ u, φ (path (ψ u)) ∂(volume.restrict (Icc 0 1))

theorem continuousAt_integralAlongTimeChange
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (φ : E → ℝ) (hφ : Continuous φ) (bound : ℝ)
    (hbound : ∀ x, ‖φ x‖ ≤ bound)
    (ψ : ℝ → unitInterval) (hψ : Continuous ψ)
    (hψ_inj : Set.InjOn ψ (Icc 0 1))
    (path : CadlagPath unitInterval E) :
    ContinuousAt (integralAlongTimeChange φ ψ) path := by
  let bad : Set unitInterval := {s | ¬ ContinuousAt path s}
  have hbad : bad.Countable := by
    simpa [bad] using path.isCadlag_toFun.countable_discontinuitySet
  let badParam : Set ℝ := Icc 0 1 ∩ ψ ⁻¹' bad
  have hbadParam : badParam.Countable := by
    apply Set.MapsTo.countable_of_injOn (f := ψ) (s := badParam) (t := bad)
    · intro u hu
      exact hu.2
    · intro u hu v hv huv
      exact hψ_inj hu.1 hv.1 huv
    · exact hbad
  have hgood : ∀ᵐ u ∂(volume.restrict (Icc 0 1)), ContinuousAt path (ψ u) := by
    filter_upwards [hbadParam.ae_notMem (volume.restrict (Icc 0 1)),
      ae_restrict_mem measurableSet_Icc] with u hu hmem
    change u ∉ badParam at hu
    by_contra hnot
    exact hu ⟨hmem, hnot⟩
  have hmeas (g : CadlagPath unitInterval E) :
      AEStronglyMeasurable (fun u : ℝ => φ (g (ψ u)))
        (volume.restrict (Icc 0 1)) := by
    apply (hφ.measurable.comp ((g.isCadlag_toFun.measurable).comp hψ.measurable))
      |>.aestronglyMeasurable
  have hbound_integrable :
      Integrable (fun _ : ℝ => bound) (volume.restrict (Icc 0 1)) :=
    integrable_const bound
  have hlim : ∀ᵐ u ∂(volume.restrict (Icc 0 1)),
      Tendsto (fun g : CadlagPath unitInterval E => φ (g (ψ u))) (𝓝 path)
        (𝓝 (φ (path (ψ u)))) := by
    filter_upwards [hgood] with u hu
    exact hφ.continuousAt.tendsto.comp
      (continuousAt_apply_of_continuousAt path (ψ u) hu)
  have h_int := tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => bound)
    (hF_meas := Filter.Eventually.of_forall hmeas)
    (h_bound := Filter.Eventually.of_forall fun g =>
      Filter.Eventually.of_forall fun u => hbound (g (ψ u)))
    hbound_integrable hlim
  change Tendsto (fun g : CadlagPath unitInterval E =>
      ∫ u, φ (g (ψ u)) ∂(volume.restrict (Icc 0 1)))
    (𝓝 path) (𝓝 (∫ u, φ (path (ψ u)) ∂(volume.restrict (Icc 0 1))))
  simpa [integralAlongTimeChange] using h_int

/-- Evaluation at a fixed time is Borel measurable for the `J₁` path space.
The proof approximates `arctan(path t)` by averages over intervals shrinking
to the right of `t`; each average is a continuous path functional by dominated
convergence. -/
theorem measurable_apply (t : unitInterval) :
    Measurable (fun path : CadlagPath unitInterval ℝ => path t) := by
  by_cases ht : t = ⊤
  · subst t
    exact continuous_apply_top.measurable
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
  have hpointwise (path : CadlagPath unitInterval ℝ) (u : ℝ)
      (hu : u ∈ Icc 0 1) :
      Tendsto (fun n => Real.arctan (path (ψ n u))) atTop
        (𝓝 (Real.arctan (path t))) := by
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
      exact Real.continuous_arctan.continuousAt.tendsto.comp
        ((path.isCadlag_toFun.isRightContinuous t).tendsto.comp htimeWithin)
  have hlimit (path : CadlagPath unitInterval ℝ) :
      Tendsto (fun n => integralAlongTimeChange Real.arctan (ψ n) path)
        atTop (𝓝 (Real.arctan (path t))) := by
    have hF_meas (n : ℕ) : AEStronglyMeasurable
        (fun u : ℝ => Real.arctan (path (ψ n u)))
        (volume.restrict (Icc 0 1)) := by
      apply (Real.measurable_arctan.comp
        ((path.isCadlag_toFun.measurable).comp (hψ_cont n).measurable)).aestronglyMeasurable
    have h_bound (n : ℕ) : ∀ᵐ u ∂(volume.restrict (Icc 0 1)),
        ‖Real.arctan (path (ψ n u))‖ ≤ Real.pi :=
      Filter.Eventually.of_forall fun u => norm_arctan_le_pi _
    have hlim : ∀ᵐ u ∂(volume.restrict (Icc 0 1)),
        Tendsto (fun n => Real.arctan (path (ψ n u))) atTop
          (𝓝 (Real.arctan (path t))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact hpointwise path u hu
    have hdc := tendsto_integral_of_dominated_convergence
      (bound := fun _ : ℝ => Real.pi)
      (F_measurable := hF_meas)
      (bound_integrable := integrable_const Real.pi)
      (h_bound := h_bound)
      (h_lim := hlim)
    simpa [integralAlongTimeChange] using hdc
  let averages : ℕ → CadlagPath unitInterval ℝ → ℝ := fun n path =>
    integralAlongTimeChange Real.arctan (ψ n) path
  have havg_cont (n : ℕ) : Continuous (averages n) :=
    continuous_iff_continuousAt.mpr fun path => by
      exact continuousAt_integralAlongTimeChange Real.arctan Real.continuous_arctan
        Real.pi norm_arctan_le_pi (ψ n) (hψ_cont n) (hψ_inj n) path
  have havg_limit : Tendsto averages atTop
      (𝓝 fun path : CadlagPath unitInterval ℝ => Real.arctan (path t)) := by
    rw [tendsto_pi_nhds]
    intro path
    exact hlimit path
  have harctan : Measurable
      (fun path : CadlagPath unitInterval ℝ => Real.arctan (path t)) :=
    measurable_of_tendsto_metrizable (fun n => (havg_cont n).measurable) havg_limit
  have hrange : Measurable
      (fun path : CadlagPath unitInterval ℝ =>
        (⟨Real.arctan (path t), Real.arctan_mem_Ioo (path t)⟩ :
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) :=
    Measurable.subtype_mk harctan
  have htan : Measurable
      (fun path : CadlagPath unitInterval ℝ =>
        Real.tanOrderIso ⟨Real.arctan (path t), Real.arctan_mem_Ioo (path t)⟩) :=
    Real.tanOrderIso.toHomeomorph.measurable.comp hrange
  convert htan using 1
  funext path
  simp [Real.arctan]

end Skorokhod

end
