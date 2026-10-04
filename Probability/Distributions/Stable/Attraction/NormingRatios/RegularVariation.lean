/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.Stable.Attraction.NormingRatios.Index
public import Probability.Distributions.Stable.Attraction.NormingRatios.UniformDefect
public import Analysis.Asymptotics.RegularVariation.AtZero

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

private theorem defectRatio_close_of_close
    {A B a b q ε c Q η : ℝ}
    (hc : 0 < c) (hb : c < b) (hq : 0 ≤ q) (hqQ : q ≤ Q)
    (hQ : 0 < Q) (hA : |A - a| < η) (hB : |B - b| < η)
    (hε : 0 < ε)
    (hη : 0 < η) (hηc : η ≤ c / 4)
    (hηQ : η * (1 + Q) ≤ ε * c / 4) (ha : a = q * b) :
    dist (A / B) q < ε := by
  have hBpos : 0 < B := by
    have hlow : b - η < B := by
      have h := abs_lt.mp hB
      linarith
    nlinarith
  have hnumerator : |A - q * B| < η * (1 + Q) := by
    have hidentity : A - q * B = (A - a) + q * (b - B) := by rw [ha]; ring
    rw [hidentity]
    have hqabs : |q| = q := abs_of_nonneg hq
    have hBA : |b - B| = |B - b| := abs_sub_comm _ _
    calc
      |(A - a) + q * (b - B)| ≤ |A - a| + |q * (b - B)| := abs_add_le _ _
      _ = |A - a| + q * |B - b| := by rw [abs_mul, hqabs, hBA]
      _ < η + Q * η := by
        apply add_lt_add hA
        calc
          q * |B - b| ≤ Q * |B - b| := mul_le_mul_of_nonneg_right hqQ (abs_nonneg _)
          _ < Q * η := mul_lt_mul_of_pos_left hB hQ
      _ = η * (1 + Q) := by ring
  have herror : |A / B - q| < ε := by
    rw [show A / B - q = (A - q * B) / B by field_simp [ne_of_gt hBpos], abs_div,
      abs_of_pos hBpos]
    apply (div_lt_iff₀ hBpos).2
    have hBstrong : 3 * c / 4 < B := by
      have h := abs_lt.mp hB
      nlinarith [hηc]
    have hprod : ε * (3 * c / 4) < ε * B :=
      mul_lt_mul_of_pos_left hBstrong hε
    nlinarith
  simpa [Real.dist_eq] using herror

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

/-- The characteristic defect ratios converge uniformly when the multiplier
ranges over `[1, 2]`. The proof uses the compact-uniform defect limit and the
first-crossing scale, and does not assume monotonicity of the norming sequence. -/
theorem IsInDomainOfAttractionAlong.tendstoUniformlyOn_normDefect_ratio_nhdsGT_zero
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    TendstoUniformlyOn
      (fun u s =>
        (1 - ‖charFun ν (s * u)‖ ^ 2) / (1 - ‖charFun ν u‖ ^ 2))
      (fun s => s ^ α) (𝓝[>] (0 : ℝ)) (Set.Icc 1 2) := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  let ψ : ℝ → ℝ := fun u => 1 - ‖charFun ν u‖ ^ 2
  let K : Set ℝ := Set.Icc 0 4
  have hKcompact : IsCompact K := by dsimp [K]; exact isCompact_Icc
  obtain ⟨c, hc, huniform⟩ := h.exists_tendstoUniformlyOn_normDefect hlimit hKcompact
  let F : ℕ → ℝ → ℝ := fun n t => (n : ℝ) * ψ ((scale n)⁻¹ * t)
  let G : ℝ → ℝ := fun t => 2 * c * |t| ^ α
  have hU : TendstoUniformlyOn F G atTop K := by simpa [F, G, ψ] using huniform
  have hscale : Tendsto scale atTop atTop := h.tendsto_scale_atTop hlimit
  let k : ℝ → ℕ := firstScaleCrossing scale hscale 2
  let r : ℝ → ℝ := fun x => scale (k x) / x
  have hk : Tendsto k atTop atTop := firstScaleCrossing_tendsto hscale 2
  have hr : Tendsto r atTop (nhds 1) :=
    firstCrossing_scale_ratio_tendsto hscale h.eventually_scale_pos
      (h.tendsto_norming_succ_ratio hlimit) 0
  have hnear : ∀ᶠ x : ℝ in atTop, 1 / 2 < r x ∧ r x < 2 := by
    have hmem : Set.Ioo (1 / 2 : ℝ) 2 ∈ 𝓝 (1 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    exact hr.eventually hmem
  have htimesK : ∀ᶠ x : ℝ in atTop,
      ∀ s ∈ Set.Icc (1 : ℝ) 2, r x ∈ K ∧ s * r x ∈ K := by
    filter_upwards [hnear] with x hx s hs
    have hrpos : 0 < r x := by linarith
    constructor
    · constructor
      · exact le_of_lt hrpos
      · change r x ≤ 4
        linarith
    · constructor
      · exact le_of_lt (mul_pos (lt_of_lt_of_le (by norm_num : 0 < (1 : ℝ)) hs.1) hrpos)
      · change s * r x ≤ 4
        nlinarith [hs.2, hx.2]
  have hGcont (a : ℝ) (ha : a ≠ 0) : ContinuousAt G a := by
    have habs : ContinuousAt (fun t : ℝ => |t|) a := continuous_abs.continuousAt
    have hpow : ContinuousAt (fun t : ℝ => t ^ α) |a| :=
      Real.continuousAt_rpow_const |a| α (Or.inl (abs_ne_zero.mpr ha))
    have hcomp : ContinuousAt (fun t : ℝ => |t| ^ α) a := hpow.comp habs
    change ContinuousAt (fun t : ℝ => (2 * c) * |t| ^ α) a
    exact continuousAt_const.mul hcomp
  have hpointOne : Tendsto (fun x : ℝ => G (r x)) atTop (nhds (2 * c)) := by
    have h := (hGcont 1 one_ne_zero).tendsto.comp hr
    have hvalue : G 1 = 2 * c := by simp [G, abs_one]
    change Tendsto (G ∘ r) atTop (nhds (2 * c))
    rw [← hvalue]
    exact h
  have hGb : ∀ᶠ x : ℝ in atTop, c < G (r x) := by
    have hlim : c < 2 * c := by linarith
    exact hpointOne.eventually (Ioi_mem_nhds hlim)
  have hFG : ∀ᶠ x : ℝ in atTop,
      ∀ t ∈ K, dist (G t) (F (k x) t) < 1 := by
    have hclose := (Metric.tendstoUniformlyOn_iff.mp hU) 1 (by norm_num)
    exact hk.eventually hclose
  have hformula : ∀ᶠ x : ℝ in atTop, 0 < x ∧ 0 < scale (k x) := by
    have hpos : ∀ᶠ x : ℝ in atTop, 0 < scale (k x) := hk.eventually h.eventually_scale_pos
    filter_upwards [eventually_gt_atTop (0 : ℝ), hpos] with x hx hs
    exact ⟨hx, hs⟩
  have hX : TendstoUniformlyOn
      (fun x s => ψ (s / x) / ψ (1 / x)) (fun s => s ^ α)
      atTop (Set.Icc 1 2) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    let Q : ℝ := 2 ^ α
    have hQ : 0 < Q := by dsimp [Q]; exact Real.rpow_pos_of_pos (by norm_num) α
    let η : ℝ := min (c / 4) (ε * c / (4 * (1 + Q)))
    have hη : 0 < η := by
      dsimp [η]
      apply lt_min
      · positivity
      · apply div_pos
        · exact mul_pos hε hc
        · positivity
    have hηc : η ≤ c / 4 := min_le_left _ _
    have hηQ : η * (1 + Q) ≤ ε * c / 4 := by
      calc
        η * (1 + Q) ≤ (ε * c / (4 * (1 + Q))) * (1 + Q) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = ε * c / 4 := by field_simp
    have hclose : ∀ᶠ x : ℝ in atTop,
        ∀ t ∈ K, dist (G t) (F (k x) t) < η := by
      have hclose' := (Metric.tendstoUniformlyOn_iff.mp hU) η hη
      exact hk.eventually hclose'
    filter_upwards [hnear, htimesK, hGb, hclose, hformula] with x hx hK hbx hFx hxf
    intro s hs
    let A := F (k x) (s * r x)
    let B := F (k x) (r x)
    let a := G (s * r x)
    let b := G (r x)
    let q := s ^ α
    have hrpos : 0 < r x := by linarith
    have hsq : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
    have hrel : a = q * b := by
      dsimp [a, b, q, G]
      rw [abs_mul, abs_of_pos hsq, abs_of_pos hrpos,
        Real.mul_rpow hsq.le hrpos.le]
      ring
    have hq : 0 ≤ q := (Real.rpow_pos_of_pos hsq α).le
    have hqQ : q ≤ Q := by
      dsimp [q, Q]
      exact Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ s) hs.2 hlimit.alpha_pos.le
    have hAclose : |A - a| < η := by
      have hKx := hK s hs
      have h := hFx (s * r x) hKx.2
      rw [Real.dist_eq] at h
      simpa [A, a, abs_sub_comm] using h
    have hBclose : |B - b| < η := by
      have hKx := hK s hs
      have h := hFx (r x) hKx.1
      rw [Real.dist_eq] at h
      simpa [B, b, abs_sub_comm] using h
    have hBpos : 0 < B := by
      have hlow : b - η < B := by
        have h := abs_lt.mp hBclose
        linarith
      have hlow' : G (r x) - η < F (k x) (r x) := by simpa [B, b] using hlow
      change 0 < F (k x) (r x)
      nlinarith [hbx, hlow', hηc]
    have hnumArg : (scale (k x))⁻¹ * (s * r x) = s / x := by
      dsimp [r]
      field_simp [ne_of_gt hxf.2, ne_of_gt hxf.1]
    have hdenArg : (scale (k x))⁻¹ * r x = 1 / x := by
      dsimp [r]
      field_simp [ne_of_gt hxf.2, ne_of_gt hxf.1]
    have hAeq : A = (k x : ℝ) * ψ (s / x) := by
      dsimp [A, F, ψ]
      rw [hnumArg]
    have hBeq : B = (k x : ℝ) * ψ (1 / x) := by
      dsimp [B, F, ψ]
      rw [hdenArg]
    have hkpos : 0 < (k x : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by
      intro hz
      have hzero : B = 0 := by rw [hBeq, hz]; simp
      exact (ne_of_gt hBpos) hzero))
    have hψden : 0 < ψ (1 / x) := by
      have hprod : 0 < (k x : ℝ) * ψ (1 / x) := by rw [← hBeq]; exact hBpos
      rcases (mul_pos_iff.mp hprod) with ⟨_, hψ⟩ | ⟨hkneg, _⟩
      · exact hψ
      · linarith
    have hcancel : A / B = ψ (s / x) / ψ (1 / x) := by
      rw [hAeq, hBeq]
      field_simp [ne_of_gt hkpos, ne_of_gt hψden]
    have hcloseRatio := defectRatio_close_of_close hc hbx hq hqQ hQ
      hAclose hBclose hε hη hηc hηQ hrel
    have htarget : dist (ψ (s / x) / ψ (1 / x)) (s ^ α) < ε := by
      rw [← hcancel]
      exact hcloseRatio
    simpa [ψ, Real.dist_eq, abs_sub_comm] using htarget
  rw [Metric.tendstoUniformlyOn_iff] at hX ⊢
  intro ε hε
  have hXε := hX ε hε
  have hinv := tendsto_inv_nhdsGT_zero.eventually hXε
  filter_upwards [hinv] with u hu s hs
  have h := hu s hs
  simpa [ψ, div_eq_mul_inv, inv_inv] using h

/-- In a nondegenerate stable domain of attraction, the squared-modulus defect
of the increment characteristic function is strictly positive at every
sufficiently small positive frequency. This follows from the positive limit
of the ratio at scale `2`; it is not an extra Tauberian hypothesis. -/
theorem IsInDomainOfAttractionAlong.eventually_pos_normDefect_nhdsGT_zero
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      0 < 1 - ‖charFun ν u‖ ^ 2 := by
  let ψ : ℝ → ℝ := fun u => 1 - ‖charFun ν u‖ ^ 2
  have hratio := h.tendsto_normDefect_ratio_nhdsGT_zero hlimit 2 (by norm_num)
  have hratioPos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < ψ (2 * u) / ψ u := by
    have hlimitPos : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
    have hevent := hratio.eventually (Ioi_mem_nhds hlimitPos)
    filter_upwards [hevent] with u hu
    exact hu
  filter_upwards [hratioPos] with u hu
  have hψnonneg : 0 ≤ ψ u := by
    dsimp [ψ]
    have hnorm := norm_charFun_le_one (μ := ν) u
    have hnormNonneg : 0 ≤ ‖charFun ν u‖ := norm_nonneg _
    nlinarith
  have hψne : ψ u ≠ 0 := by
    intro hz
    have hzero : ψ (2 * u) / ψ u = 0 := by rw [hz]; simp
    rw [hzero] at hu
    exact (lt_irrefl 0) hu
  have hψpos : 0 < ψ u := lt_or_gt_of_ne hψne |>.resolve_left (by
    intro hneg
    exact (not_lt_of_ge hψnonneg) hneg)
  exact hψpos

/-- A stable domain of attraction makes the squared-modulus characteristic
defect regularly varying at zero. This packages the fixed-multiplier limits
and the eventual positivity needed by inverse Tauberian arguments. -/
theorem IsInDomainOfAttractionAlong.isRegularlyVarying_normDefect_atZero
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    Asymptotics.IsRegularlyVaryingAtZero
      (fun u => 1 - ‖charFun ν u‖ ^ 2) α := by
  refine ⟨h.eventually_pos_normDefect_nhdsGT_zero hlimit, ?_⟩
  intro s hs
  exact h.tendsto_normDefect_ratio_nhdsGT_zero hlimit s hs

end ProbabilityTheory

end
