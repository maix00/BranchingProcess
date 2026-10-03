/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.Stable.Attraction.NormingRatios.Index
public import Probability.Distributions.Stable.Attraction.NormingRatios.UniformDefect

/-!
# Continuous-frequency regular variation from norming ratios

Compact-uniform characteristic-function defects and a first-crossing scale
index transfer the discrete norming asymptotics to all sufficiently small
frequencies. The first-crossing construction does not assume monotonicity.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

private noncomputable def squaredModulusDefect (ν : Measure ℝ) (u : ℝ) : ℝ :=
  1 - ‖charFun ν u‖ ^ 2

private theorem exists_scale_crossing {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) (N : ℕ) (x : ℝ) :
    ∃ n, N ≤ n ∧ x ≤ scale n := by
  have hN : ∀ᶠ n : ℕ in atTop, N ≤ n :=
    eventually_atTop.2 ⟨N, fun n hn => hn⟩
  have hx : ∀ᶠ n : ℕ in atTop, x < scale n := hscale.eventually_gt_atTop x
  obtain ⟨n, hnN, hnx⟩ := (hN.and hx).exists
  exact ⟨n, hnN, le_of_lt hnx⟩

private noncomputable def firstScaleCrossing (scale : ℕ → ℝ)
    (hscale : Tendsto scale atTop atTop) (N : ℕ) (x : ℝ) : ℕ :=
  Nat.find (exists_scale_crossing hscale N x)

private theorem firstScaleCrossing_spec {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) (N : ℕ) (x : ℝ) :
    N ≤ firstScaleCrossing scale hscale N x ∧
      x ≤ scale (firstScaleCrossing scale hscale N x) :=
  Nat.find_spec (exists_scale_crossing hscale N x)

private theorem firstScaleCrossing_tendsto {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) (N : ℕ) :
    Tendsto (firstScaleCrossing scale hscale N) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · let S : Finset ℕ := Finset.range k
    have hS : S.Nonempty := by
      refine ⟨0, ?_⟩
      simp [S]
      omega
    let M : ℝ := S.sup' hS scale
    have hlarge : ∀ᶠ x : ℝ in atTop, M < x := eventually_gt_atTop M
    filter_upwards [hlarge] with x hx
    by_contra hnot
    have hcross : firstScaleCrossing scale hscale N x < k := Nat.lt_of_not_ge hnot
    have hmem : firstScaleCrossing scale hscale N x ∈ S := by
      simp [S, hcross]
    have hscaleLE : scale (firstScaleCrossing scale hscale N x) ≤ M := by
      dsimp [M]
      exact Finset.le_sup' (s := S) (f := scale) hmem
    have hcrossSpec := (firstScaleCrossing_spec hscale N x).2
    dsimp [M] at hx
    linarith

private theorem tendstoUniformlyOn_eval_of_tendsto
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {K : Set ℝ}
    {idx : ℝ → ℕ} {time : ℝ → ℝ} {l : ℝ}
    (hU : TendstoUniformlyOn f g atTop K)
    (hidx : Tendsto idx atTop atTop)
    (hpoint : Tendsto (fun x => g (time x)) atTop (nhds l))
    (hK : ∀ᶠ x in atTop, time x ∈ K) :
    Tendsto (fun x => f (idx x) (time x)) atTop (nhds l) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  have hpointClose : ∀ᶠ i in atTop, dist l (g (time i)) < ε / 2 :=
    (hpoint.eventually (Metric.ball_mem_nhds _ hhalf)).mono fun i hi => by
      simpa [dist_comm] using hi
  have huniformIndex : ∀ᶠ i in atTop,
      ∀ t ∈ K, dist (g t) (f (idx i) t) < ε / 2 := by
    have huniformN := (Metric.tendstoUniformlyOn_iff.mp hU) (ε / 2) hhalf
    exact hidx.eventually huniformN
  filter_upwards [hpointClose, huniformIndex, hK] with x hi hu hti
  calc
    dist (f (idx x) (time x)) l ≤
        dist (f (idx x) (time x)) (g (time x)) + dist (g (time x)) l :=
          dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · simpa [dist_comm] using hu (time x) hti
      · simpa [dist_comm] using hi
    _ = ε := by ring

private theorem firstCrossing_scale_ratio_tendsto {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < scale n)
    (hsucc : Tendsto (fun n : ℕ => scale (n + 1) / scale n) atTop (nhds 1))
    (N : ℕ) :
    Tendsto (fun x : ℝ =>
      scale (firstScaleCrossing scale hscale (N + 2) x) / x)
      atTop (nhds 1) := by
  let crossing := firstScaleCrossing scale hscale (N + 2)
  have hcrossTop : Tendsto crossing atTop atTop :=
    firstScaleCrossing_tendsto hscale (N + 2)
  have hpredTop : Tendsto (fun x : ℝ => crossing x - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    have hcross := (tendsto_atTop.1 hcrossTop) (k + 1)
    filter_upwards [hcross] with x hx
    omega
  have hsuccPred : Tendsto
      (fun x : ℝ => scale ((crossing x - 1) + 1) / scale (crossing x - 1))
      atTop (nhds 1) := hsucc.comp hpredTop
  have hpredEq : (fun x : ℝ =>
      scale ((crossing x - 1) + 1) / scale (crossing x - 1)) =ᶠ[atTop]
      fun x => scale (crossing x) / scale (crossing x - 1) := by
    filter_upwards [hcrossTop.eventually (eventually_ge_atTop (N + 2))] with x hx
    congr 1
    exact congrArg scale (Nat.sub_add_cancel (show 1 ≤ crossing x by omega))
  have hupperLimit : Tendsto
      (fun x : ℝ => scale (crossing x) / scale (crossing x - 1)) atTop (nhds 1) :=
    hsuccPred.congr' hpredEq
  have hbounds : ∀ᶠ x : ℝ in atTop,
      1 ≤ scale (crossing x) / x ∧
        scale (crossing x) / x ≤ scale (crossing x) / scale (crossing x - 1) := by
    have hposCurrent : ∀ᶠ x : ℝ in atTop, 0 < scale (crossing x) :=
      hcrossTop.eventually hpos
    have hposPrevious : ∀ᶠ x : ℝ in atTop, 0 < scale (crossing x - 1) :=
      hpredTop.eventually hpos
    filter_upwards [eventually_gt_atTop (0 : ℝ), hcrossTop.eventually
        (eventually_ge_atTop (N + 3)), hposCurrent, hposPrevious]
      with x hx hcrossN hposN hposPred
    have hpredN' : N + 2 ≤ crossing x - 1 := by
      have hsub : crossing x - 1 + 1 = crossing x :=
        Nat.sub_add_cancel (show 1 ≤ crossing x by omega)
      omega
    have hxle := (firstScaleCrossing_spec hscale (N + 2) x).2
    have hpredlt : scale (crossing x - 1) < x := by
      by_contra hnot
      have hpredltidx : crossing x - 1 < crossing x :=
        Nat.sub_lt (by omega) (by norm_num)
      have hmin := Nat.find_min
        (exists_scale_crossing hscale (N + 2) x) hpredltidx
      apply hmin
      exact ⟨hpredN', le_of_not_gt hnot⟩
    have hposCurrent : 0 < scale (crossing x) := hposN
    have hposPrevious : 0 < scale (crossing x - 1) := by
      exact hposPred
    constructor
    · exact (le_div_iff₀ hx).2 (by nlinarith)
    · apply (div_le_div_iff₀ hx hposPrevious).2
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt hpredlt) hposCurrent.le
      nlinarith
  have hlower : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hupper := hupperLimit
  have hlow : ∀ᶠ x : ℝ in atTop,
      1 ≤ scale (crossing x) / x := hbounds.mono fun x hx => hx.1
  have hupp : ∀ᶠ x : ℝ in atTop,
      scale (crossing x) / x ≤ scale (crossing x) / scale (crossing x - 1) :=
    hbounds.mono fun x hx => hx.2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper hlow hupp

/-- The squared-modulus defect of an increment law in the domain of attraction
of an `α`-stable law is regularly varying at zero with index `α`. The proof
uses a first-crossing index, so the norming sequence need not be monotone. -/
theorem IsInDomainOfAttractionAlong.tendsto_normDefect_ratio_nhdsGT_zero
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (s : ℝ) (hs : 0 < s) :
    Tendsto
      (fun u : ℝ =>
        (1 - ‖charFun ν (s * u)‖ ^ 2) /
          (1 - ‖charFun ν u‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (nhds (s ^ α)) := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  let ψ : ℝ → ℝ := fun u => 1 - ‖charFun ν u‖ ^ 2
  have hscale : Tendsto scale atTop atTop := h.tendsto_scale_atTop hlimit
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := h.eventually_scale_pos
  have hsucc : Tendsto (fun n : ℕ => scale (n + 1) / scale n) atTop (nhds 1) :=
    h.tendsto_norming_succ_ratio hlimit
  let k : ℝ → ℕ := firstScaleCrossing scale hscale 2
  let r : ℝ → ℝ := fun x => scale (k x) / x
  have hk : Tendsto k atTop atTop := firstScaleCrossing_tendsto hscale 2
  have hr : Tendsto r atTop (nhds 1) :=
    firstCrossing_scale_ratio_tendsto hscale hscalePos hsucc 0
  have hkpos : ∀ᶠ x : ℝ in atTop, 0 < scale (k x) := hk.eventually hscalePos

  let K : Set ℝ := Set.Icc 0 (2 * max s 1)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc
  obtain ⟨c, hc, huniform⟩ := h.exists_tendstoUniformlyOn_normDefect hlimit hKcompact
  let F : ℕ → ℝ → ℝ := fun n t => (n : ℝ) *
    (1 - ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2)
  let G : ℝ → ℝ := fun t => 2 * c * |t| ^ α
  have hU : TendstoUniformlyOn F G atTop K := by
    simpa [F, G] using huniform

  have hGcont (a : ℝ) (ha : a ≠ 0) : ContinuousAt G a := by
    have habs : ContinuousAt (fun t : ℝ => |t|) a := continuous_abs.continuousAt
    have hpow : ContinuousAt (fun t : ℝ => t ^ α) |a| :=
      Real.continuousAt_rpow_const |a| α (Or.inl (abs_ne_zero.mpr ha))
    have hcomp : ContinuousAt (fun t : ℝ => |t| ^ α) a := hpow.comp habs
    change ContinuousAt (fun t : ℝ => (2 * c) * |t| ^ α) a
    exact continuousAt_const.mul hcomp

  have hnear : ∀ᶠ x : ℝ in atTop, 1 / 2 < r x ∧ r x < 2 := by
    have hmem : Set.Ioo (1 / 2 : ℝ) 2 ∈ 𝓝 (1 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    have hmem := hr.eventually hmem
    filter_upwards [hmem] with x hx
    exact hx
  have htimesK : ∀ᶠ x : ℝ in atTop, r x ∈ K ∧ s * r x ∈ K := by
    filter_upwards [hnear] with x hx
    have hrpos : 0 < r x := by linarith
    have hmax : 1 ≤ max s 1 := le_max_right _ _
    constructor
    · constructor
      · exact le_of_lt hrpos
      · nlinarith [hx.2, hmax]
    · constructor
      · exact le_of_lt (mul_pos hs hrpos)
      · nlinarith [hx.2, le_max_left s 1]

  have htimeS : Tendsto (fun x : ℝ => s * r x) atTop (nhds s) := by
    simpa using tendsto_const_nhds.mul hr
  have hpointS : Tendsto (fun x : ℝ => G (s * r x)) atTop
      (nhds (2 * c * s ^ α)) := by
    have h := (hGcont s hs.ne').tendsto.comp htimeS
    have hvalue : G s = 2 * c * s ^ α := by simp [G, abs_of_pos hs]
    change Tendsto (G ∘ (fun x : ℝ => s * r x)) atTop (nhds (2 * c * s ^ α))
    rw [← hvalue]
    exact h
  have hpointOne : Tendsto (fun x : ℝ => G (r x)) atTop (nhds (2 * c)) := by
    have h := (hGcont 1 one_ne_zero).tendsto.comp hr
    have hvalue : G 1 = 2 * c := by simp [G, abs_one]
    change Tendsto (G ∘ r) atTop (nhds (2 * c))
    rw [← hvalue]
    exact h
  have hnumEval : Tendsto (fun x : ℝ => F (k x) (s * r x)) atTop
      (nhds (2 * c * s ^ α)) :=
    tendstoUniformlyOn_eval_of_tendsto hU hk hpointS
      (htimesK.mono fun x hx => hx.2)
  have hdenEval : Tendsto (fun x : ℝ => F (k x) (r x)) atTop
      (nhds (2 * c)) :=
    tendstoUniformlyOn_eval_of_tendsto hU hk hpointOne
      (htimesK.mono fun x hx => hx.1)

  have hnumEq : (fun x : ℝ => F (k x) (s * r x)) =ᶠ[atTop]
      fun x => (k x : ℝ) * ψ (s / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hkpos] with x hx hbx
    have harg : (scale (k x))⁻¹ * (s * r x) = s / x := by
      dsimp [r]
      field_simp [ne_of_gt hbx, ne_of_gt hx]
    simp only [F, ψ, harg]
  have hdenEq : (fun x : ℝ => F (k x) (r x)) =ᶠ[atTop]
      fun x => (k x : ℝ) * ψ (1 / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hkpos] with x hx hbx
    have harg : (scale (k x))⁻¹ * r x = 1 / x := by
      dsimp [r]
      field_simp [ne_of_gt hbx, ne_of_gt hx]
    simp only [F, ψ, harg]
  have hnum : Tendsto (fun x : ℝ => (k x : ℝ) * ψ (s / x)) atTop
      (nhds (2 * c * s ^ α)) := hnumEval.congr' hnumEq
  have hden : Tendsto (fun x : ℝ => (k x : ℝ) * ψ (1 / x)) atTop
      (nhds (2 * c)) := hdenEval.congr' hdenEq
  have hcne : (2 * c : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num) hc)
  have hscaledRatio : Tendsto
      (fun x : ℝ => ((k x : ℝ) * ψ (s / x)) / ((k x : ℝ) * ψ (1 / x)))
      atTop (nhds ((2 * c * s ^ α) / (2 * c))) := hnum.div hden hcne
  have hkNatPos : ∀ᶠ x : ℝ in atTop, 0 < k x := by
    exact hk.eventually (eventually_gt_atTop (0 : ℕ))
  have hcancel : (fun x : ℝ =>
      ((k x : ℝ) * ψ (s / x)) / ((k x : ℝ) * ψ (1 / x))) =ᶠ[atTop]
      fun x => ψ (s / x) / ψ (1 / x) := by
    filter_upwards [hkNatPos] with x hx
    have hxne : (k x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    field_simp [hxne]
  have hratioX : Tendsto (fun x : ℝ => ψ (s / x) / ψ (1 / x)) atTop
      (nhds (s ^ α)) := by
    have h := hscaledRatio.congr' hcancel
    have hlimit : (2 * c * s ^ α) / (2 * c) = s ^ α := by
      field_simp [hc.ne']
    simpa only [hlimit] using h
  have hratioU := hratioX.comp tendsto_inv_nhdsGT_zero
  have hconvert : (fun u : ℝ => ψ (s * u) / ψ u) =ᶠ[𝓝[>] (0 : ℝ)]
      fun u => ψ (s / u⁻¹) / ψ (1 / u⁻¹) := by
    filter_upwards [] with u
    simp [div_eq_mul_inv, inv_inv]
  have hfinal := hratioU.congr' hconvert.symm
  simpa [ψ] using hfinal

end ProbabilityTheory

end
