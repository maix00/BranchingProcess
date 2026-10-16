/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity
public import Topology.Cadlag.Skorokhod.TimeChange.Convergence

/-!
# Limits of cumulative Skorokhod time changes

A summable logarithmic distortion budget bounds every cumulative secant slope
away from zero. Therefore the uniform limit of cumulative clocks remains a
strictly increasing endpoint-preserving homeomorphism.
-/

@[expose] public section

open Filter
open scoped NNReal

namespace Skorokhod

namespace TimeChange

/-- Summably small local logarithmic distortions yield a limiting Skorokhod
time change, and the cumulative clocks converge to it uniformly. -/
theorem exists_timeChange_limit_of_summable_logDistortion
    (clocks : ℕ → TimeChange) (error : ℕ → ℝ≥0)
    (hstep : ∀ n, (clocks n).logDistortion ≤ error n)
    (herror : Summable error) :
    ∃ limit : TimeChange,
      TendstoUniformly (fun n t => cumulative clocks n t) limit atTop := by
  obtain ⟨limitMap, huniform⟩ :=
    exists_uniform_limit_cumulative_of_summable_logDistortion clocks error hstep herror
  have hpoint (u : unitInterval) : Tendsto (fun n => cumulative clocks n u)
      atTop (nhds (limitMap u)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hnear := Metric.tendstoUniformly_iff.mp huniform ε hε
    filter_upwards [hnear] with n hn
    simpa [dist_comm] using hn u
  have hbot : limitMap ⊥ = ⊥ := by
    have hconstant : Tendsto
        (fun n => (cumulative clocks n).toContinuousMap ⊥) atTop (nhds ⊥) := by
      have heq : (fun n => (cumulative clocks n).toContinuousMap ⊥) =
          fun _ : ℕ => (⊥ : unitInterval) := by
        funext n
        change cumulative clocks n ⊥ = ⊥
        exact TimeChange.apply_bot _
      rw [heq]
      exact tendsto_const_nhds
    exact (tendsto_nhds_unique hconstant (hpoint ⊥)).symm
  have htop : limitMap ⊤ = ⊤ := by
    have hconstant : Tendsto
        (fun n => (cumulative clocks n).toContinuousMap ⊤) atTop (nhds ⊤) := by
      have heq : (fun n => (cumulative clocks n).toContinuousMap ⊤) =
          fun _ : ℕ => (⊤ : unitInterval) := by
        funext n
        change cumulative clocks n ⊤ = ⊤
        exact TimeChange.apply_top _
      rw [heq]
      exact tendsto_const_nhds
    exact (tendsto_nhds_unique hconstant (hpoint ⊤)).symm
  let total : ℝ≥0 := ∑' n, error n
  have hstrict : StrictMono (fun t : unitInterval => limitMap t) := by
    intro s t hst
    have hstReal : (s : ℝ) < (t : ℝ) := hst
    have hdenom : 0 < (t : ℝ) - (s : ℝ) := sub_pos.mpr hstReal
    have htotalNonneg : 0 ≤ (total : ℝ) := NNReal.coe_nonneg _
    let lower : ℝ := Real.exp (-(total : ℝ))
    have hlowerPos : 0 < lower := Real.exp_pos _
    have hsecantLower : ∀ n,
        lower * ((t : ℝ) - (s : ℝ)) ≤
          ((cumulative clocks n t : unitInterval) : ℝ) -
            ((cumulative clocks n s : unitInterval) : ℝ) := by
      intro n
      let τ := cumulative clocks n
      have hglobal : τ.logDistortion ≤ ENNReal.ofReal (total : ℝ) := by
        simpa [τ, total] using
          logDistortion_cumulative_le_tsum clocks error hstep herror n
      have hp : ENNReal.ofReal (τ.logSecantDistortion s t) ≤ τ.logDistortion :=
        le_iSup (fun p : SecantPair => ENNReal.ofReal
          (τ.logSecantDistortion p.1.1 p.1.2)) ⟨(s, t), hst⟩
      have hlog : τ.logSecantDistortion s t ≤ (total : ℝ) :=
        (ENNReal.ofReal_le_ofReal_iff htotalNonneg).mp (hp.trans hglobal)
      have hlogLower : -(total : ℝ) ≤ Real.log (τ.secantSlope s t) :=
        (abs_le.mp hlog).1
      have hslopePos : 0 < τ.secantSlope s t := τ.secantSlope_pos hst
      have hslopeLower : lower ≤ τ.secantSlope s t := by
        calc
          lower = Real.exp (-(total : ℝ)) := rfl
          _ ≤ Real.exp (Real.log (τ.secantSlope s t)) :=
            Real.exp_le_exp.mpr hlogLower
          _ = τ.secantSlope s t := Real.exp_log hslopePos
      have hratio : lower ≤
          (((τ t : unitInterval) : ℝ) - ((τ s : unitInterval) : ℝ)) /
            ((t : ℝ) - (s : ℝ)) := by
        simpa [τ, secantSlope] using hslopeLower
      have hnum := (le_div_iff₀ hdenom).mp hratio
      simpa [lower] using hnum
    have hpt (u : unitInterval) : Tendsto
        (fun n => ((cumulative clocks n u : unitInterval) : ℝ)) atTop
        (nhds ((limitMap u : unitInterval) : ℝ)) := by
      exact continuous_subtype_val.continuousAt.tendsto.comp (hpoint u)
    have hdiff : Tendsto
        (fun n => ((cumulative clocks n t : unitInterval) : ℝ) -
          ((cumulative clocks n s : unitInterval) : ℝ)) atTop
        (nhds (((limitMap t : unitInterval) : ℝ) -
          ((limitMap s : unitInterval) : ℝ))) :=
      (hpt t).sub (hpt s)
    have hbound : ∀ᶠ n in atTop,
        ((cumulative clocks n t : unitInterval) : ℝ) -
          ((cumulative clocks n s : unitInterval) : ℝ) ∈
            Set.Ici (lower * ((t : ℝ) - (s : ℝ))) :=
      Filter.Eventually.of_forall fun n => hsecantLower n
    have hlimitBound := isClosed_Ici.mem_of_tendsto hdiff hbound
    have hpositive : 0 <
        ((limitMap t : unitInterval) : ℝ) - ((limitMap s : unitInterval) : ℝ) :=
      lt_of_lt_of_le (mul_pos hlowerPos hdenom) hlimitBound
    change limitMap s < limitMap t
    exact_mod_cast (sub_pos.mp hpositive)
  have himage := Continuous.image_Icc_of_strictMono
    (f := fun t : unitInterval => limitMap t) (a := ⊥) (b := ⊤)
    limitMap.continuous hstrict
  have himage_univ : limitMap '' (Set.univ : Set unitInterval) = Set.univ := by
    simpa [hbot, htop] using himage
  have hsurj : Function.Surjective limitMap := by
    intro y
    have hy : y ∈ limitMap '' (Set.univ : Set unitInterval) := by
      rw [himage_univ]
      exact Set.mem_univ y
    rcases (Set.mem_image limitMap Set.univ y).mp hy with ⟨x, hx, hxy⟩
    exact ⟨x, hxy⟩
  let orderIso : unitInterval ≃o unitInterval :=
    OrderIso.ofSurjective (OrderEmbedding.ofStrictMono limitMap hstrict) hsurj
  let limit : TimeChange := ⟨orderIso.toHomeomorph, orderIso.strictMono⟩
  refine ⟨limit, ?_⟩
  have hlimitMap : (limit : unitInterval → unitInterval) = limitMap := by
    funext t
    rfl
  simpa [hlimitMap] using huniform

end TimeChange

end Skorokhod
