/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation.AtZero

/-!
# Potter bounds at zero from compact-uniform ratios

The dyadic argument here does not assume monotonicity. Its local input is
uniform control of ratios on `[1, 2]`; this is stronger than pointwise regular
variation and is supplied by the compact-uniform characteristic-defect limit.
-/

open Filter Set
open scoped Topology

@[expose] public section

namespace Asymptotics.IsRegularlyVaryingAtZero

/-- A two-sided Potter bound at zero from uniform ratio convergence on the
compact multiplier interval `[1, 2]`. No monotonicity assumption is made. The
constant on the lower bound accounts for the final residual dyadic interval. -/
theorem exists_potter_bound_of_uniform_ratio
    {f : ℝ → ℝ} {ρ : ℝ}
    (hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u)
    (huniform : TendstoUniformlyOn
      (fun u r => f (r * u) / f u) (fun r => r ^ ρ)
      (𝓝[>] (0 : ℝ)) (Set.Icc 1 2))
    (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ) :
    ∃ U : ℝ, 0 < U ∧ (∀ ⦃u : ℝ⦄, 0 < u → u < U → 0 < f u) ∧
      ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v < U →
      (1 / (2 * 2 ^ (ρ - δ))) * (v / u) ^ (ρ - δ) ≤ f v / f u ∧
        f v / f u ≤ (2 ^ ρ + 1) * (v / u) ^ (ρ + δ) := by
  let p : ℝ := ρ - δ
  let q : ℝ := ρ + δ
  let a : ℝ := (2 : ℝ) ^ p
  let b : ℝ := (2 : ℝ) ^ q
  let D : ℝ := (2 : ℝ) ^ ρ + 1
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have ha : 0 < a := by dsimp [a]; exact Real.rpow_pos_of_pos (by norm_num) p
  have hb : 0 < b := by dsimp [b]; exact Real.rpow_pos_of_pos (by norm_num) q
  have hD : 0 < D := by dsimp [D]; positivity
  have hpowLo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have hpowHi : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
  have hpowMid : 0 < (2 : ℝ) ^ ρ := Real.rpow_pos_of_pos (by norm_num) ρ
  have hlo : (2 : ℝ) ^ p < (2 : ℝ) ^ ρ := by
    dsimp [p]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hhi : (2 : ℝ) ^ ρ < (2 : ℝ) ^ q := by
    dsimp [q]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by linarith)
  let η : ℝ := min ((2 : ℝ) ^ ρ - (2 : ℝ) ^ p) ((2 : ℝ) ^ q - (2 : ℝ) ^ ρ)
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min
    · linarith
    · linarith
  have hres : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      ∀ r ∈ Set.Icc (1 : ℝ) 2,
      dist (f (r * u) / f u) (r ^ ρ) < 1 / 2 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp huniform) (1 / 2) (by norm_num)
    filter_upwards [h] with u hu r hr
    simpa [dist_comm] using hu r hr
  have hdouble : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      dist (f (2 * u) / f u) ((2 : ℝ) ^ ρ) < η := by
    have h := (Metric.tendstoUniformlyOn_iff.mp huniform) η hη
    filter_upwards [h] with u hu
    simpa [dist_comm] using hu 2 ⟨by norm_num, by norm_num⟩
  have hgood : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      0 < f u ∧
        (∀ r ∈ Set.Icc (1 : ℝ) 2,
          1 / 2 ≤ f (r * u) / f u ∧ f (r * u) / f u ≤ D) ∧
        a ≤ f (2 * u) / f u ∧ f (2 * u) / f u ≤ b := by
    filter_upwards [hpos, hres, hdouble] with u hfu hresU hdoubleU
    refine ⟨hfu, ?_, ?_⟩
    · intro r hr
      have hrhoLo : 1 ≤ r ^ ρ := by
        simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hr.1 hρ.le
      have hrhoHi : r ^ ρ ≤ (2 : ℝ) ^ ρ :=
        Real.rpow_le_rpow (by linarith [hr.1]) hr.2 hρ.le
      have habs := abs_lt.mp (by simpa [Real.dist_eq] using hresU r hr)
      constructor <;> nlinarith [habs.1, habs.2]
    · have habs := abs_lt.mp (by simpa [Real.dist_eq] using hdoubleU)
      have hηlo : η ≤ (2 : ℝ) ^ ρ - (2 : ℝ) ^ p := min_le_left _ _
      have hηhi : η ≤ (2 : ℝ) ^ q - (2 : ℝ) ^ ρ := min_le_right _ _
      constructor <;> nlinarith [habs.1, habs.2, hηlo, hηhi]
  have hgoodSet : {u : ℝ | 0 < f u ∧
      (∀ r ∈ Set.Icc (1 : ℝ) 2,
        1 / 2 ≤ f (r * u) / f u ∧ f (r * u) / f u ≤ D) ∧
      a ≤ f (2 * u) / f u ∧ f (2 * u) / f u ≤ b} ∈ 𝓝[>] (0 : ℝ) := hgood
  obtain ⟨U, hUmem, hUsubset⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset (a := (0 : ℝ))).mp hgoodSet
  have hU : 0 < U := hUmem
  have hlocal (w : ℝ) (hw : 0 < w) (hwU : w < U) :
      0 < f w ∧
        (∀ r ∈ Set.Icc (1 : ℝ) 2,
          1 / 2 ≤ f (r * w) / f w ∧ f (r * w) / f w ≤ D) ∧
        a ≤ f (2 * w) / f w ∧ f (2 * w) / f w ≤ b := by
    have h := hUsubset ⟨hw, hwU⟩
    simpa using h
  refine ⟨U, hU, ?_⟩
  constructor
  · intro w hw hwU
    exact (hlocal w hw hwU).1
  intro u v hu huv hvU
  have hfu : 0 < f u := (hlocal u hu (lt_of_le_of_lt huv hvU)).1
  have hz : 1 ≤ v / u := by
    apply (le_div_iff₀ hu).2
    nlinarith
  obtain ⟨N, hNlo, hNhi⟩ := exists_nat_pow_near hz (by norm_num : (1 : ℝ) < 2)
  let w : ℝ := (2 : ℝ) ^ N * u
  have hwpos : 0 < w := by dsimp [w]; positivity
  have hwle : w ≤ v := by
    dsimp [w]
    have hmul := mul_le_mul_of_nonneg_right hNlo hu.le
    calc
      (2 : ℝ) ^ N * u ≤ (v / u) * u := hmul
      _ = v := div_mul_cancel₀ v hu.ne'
  have hwU : w < U := lt_of_le_of_lt hwle hvU
  have hpowLe : ∀ n : ℕ, (2 : ℝ) ^ n * u ≤ v →
      a ^ n ≤ f ((2 : ℝ) ^ n * u) / f u ∧
        f ((2 : ℝ) ^ n * u) / f u ≤ b ^ n := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hfu' : 0 < f u := (hlocal u hu (lt_of_le_of_lt huv hvU)).1
        simp [hfu'.ne']
    | succ n ih =>
        intro hn
        have hpowMono : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := by
          calc
            (2 : ℝ) ^ n = (2 : ℝ) ^ n * 1 := by ring
            _ ≤ (2 : ℝ) ^ n * 2 :=
              mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) ≤ 2)
                (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
            _ = (2 : ℝ) ^ (n + 1) := by rw [pow_succ]
        have hnprev : (2 : ℝ) ^ n * u ≤ v := by
          calc
            (2 : ℝ) ^ n * u ≤ 2 ^ (n + 1) * u :=
              mul_le_mul_of_nonneg_right hpowMono hu.le
            _ ≤ v := hn
        obtain ⟨hprevLo, hprevHi⟩ := ih hnprev
        let z : ℝ := (2 : ℝ) ^ n * u
        have hzpos : 0 < z := by dsimp [z]; positivity
        have hzU : z < U := lt_of_le_of_lt hnprev hvU
        have hstep := hlocal z hzpos hzU
        have hnextArg : 2 * z = (2 : ℝ) ^ (n + 1) * u := by
          dsimp [z]
          rw [pow_succ]
          ring
        have hstepLo : a ≤ f ((2 : ℝ) ^ (n + 1) * u) / f z := by
          rw [← hnextArg]
          exact hstep.2.2.1
        have hstepHi : f ((2 : ℝ) ^ (n + 1) * u) / f z ≤ b := by
          rw [← hnextArg]
          exact hstep.2.2.2
        have hfactor : f ((2 : ℝ) ^ (n + 1) * u) / f u =
            (f ((2 : ℝ) ^ (n + 1) * u) / f z) * (f z / f u) := by
          field_simp [ne_of_gt hstep.1, ne_of_gt hfu]
        constructor
        · calc
            a ^ (n + 1) = a * a ^ n := by rw [pow_succ]; ring
            _ ≤ (f ((2 : ℝ) ^ (n + 1) * u) / f z) * (f z / f u) :=
              mul_le_mul hstepLo hprevLo (pow_nonneg ha.le n)
                (le_trans ha.le hstepLo)
            _ = f ((2 : ℝ) ^ (n + 1) * u) / f u := hfactor.symm
        · calc
            f ((2 : ℝ) ^ (n + 1) * u) / f u =
                (f ((2 : ℝ) ^ (n + 1) * u) / f z) * (f z / f u) := hfactor
            _ ≤ b * b ^ n :=
              mul_le_mul hstepHi hprevHi
                (div_nonneg hstep.1.le hfu.le) hb.le
            _ = b ^ (n + 1) := by rw [pow_succ]; ring
  have hiterate := hpowLe N (by simpa [w] using hwle)
  let r : ℝ := v / w
  have hrlo : 1 ≤ r := by
    dsimp [r]
    apply (one_le_div₀ hwpos).2
    exact hwle
  have htwoW : v < 2 * w := by
    dsimp [w] at hNhi ⊢
    have hmul := (div_lt_iff₀ hu).1 hNhi
    rw [pow_succ] at hmul
    nlinarith
  have hrhi : r ≤ 2 := by
    dsimp [r]
    exact (div_le_iff₀ hwpos).2 (le_of_lt htwoW)
  have hrmem : r ∈ Set.Icc (1 : ℝ) 2 := ⟨hrlo, hrhi⟩
  have hres := (hlocal w hwpos hwU).2.1 r hrmem
  have hfw : 0 < f w := (hlocal w hwpos hwU).1
  have hrEq : r * w = v := by
    dsimp [r]
    exact div_mul_cancel₀ v hwpos.ne'
  have hresV : (1 / 2 : ℝ) ≤ f v / f w ∧ f v / f w ≤ D := by
    simpa [hrEq] using hres
  have hfactorFinal : f v / f u = (f v / f w) * (f w / f u) := by
    field_simp [ne_of_gt hfw, ne_of_gt hfu]
  have hratioLower : (1 / 2 : ℝ) * a ^ N ≤ f v / f u := by
    calc
      (1 / 2 : ℝ) * a ^ N ≤ (f v / f w) * (f w / f u) :=
        mul_le_mul hresV.1 hiterate.1 (pow_nonneg ha.le N)
          (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hresV.1)
      _ = f v / f u := hfactorFinal.symm
  have hratioUpper : f v / f u ≤ D * b ^ N := by
    calc
      f v / f u = (f v / f w) * (f w / f u) := hfactorFinal
      _ ≤ D * b ^ N := mul_le_mul hresV.2 hiterate.2
          (div_nonneg hfw.le hfu.le) hD.le
  have hpowNlo : ((2 : ℝ) ^ N) ^ p ≤ (v / u) ^ p :=
    Real.rpow_le_rpow (by positivity) hNlo hp.le
  have hpowNhi : (v / u) ^ q ≤ ((2 : ℝ) ^ (N + 1)) ^ q :=
    Real.rpow_le_rpow (by positivity) hNhi.le hq.le
  have hpowCommp : a ^ N = ((2 : ℝ) ^ N) ^ p := by
    dsimp [a]
    exact Real.rpow_pow_comm (by norm_num) p N
  have hpowCommq : b ^ N = ((2 : ℝ) ^ N) ^ q := by
    dsimp [b]
    exact Real.rpow_pow_comm (by norm_num) q N
  have hupperPow : b ^ N ≤ (v / u) ^ q := by
    rw [hpowCommq]
    exact Real.rpow_le_rpow (by positivity) hNlo hq.le
  have hlowerPow : (1 / (2 * a) : ℝ) * (v / u) ^ p ≤
      (1 / 2 : ℝ) * a ^ N := by
    have hpowNhi' : (v / u) ^ p ≤ ((2 : ℝ) ^ (N + 1)) ^ p :=
      Real.rpow_le_rpow (by positivity) hNhi.le hp.le
    have hpowSucc : ((2 : ℝ) ^ (N + 1)) ^ p = a * ((2 : ℝ) ^ N) ^ p := by
      dsimp [a]
      rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
      ring
    calc
      (1 / (2 * a) : ℝ) * (v / u) ^ p ≤
          (1 / (2 * a) : ℝ) * ((2 : ℝ) ^ (N + 1)) ^ p :=
        mul_le_mul_of_nonneg_left hpowNhi' (by positivity)
      _ = (1 / (2 * a) : ℝ) * (a * ((2 : ℝ) ^ N) ^ p) := by rw [hpowSucc]
      _ = (1 / 2 : ℝ) * a ^ N := by
        rw [hpowCommp]
        field_simp [ne_of_gt ha]
  refine ⟨?_, ?_⟩
  · exact hlowerPow.trans hratioLower
  · calc
      f v / f u ≤ D * b ^ N := hratioUpper
      _ ≤ D * (v / u) ^ q := mul_le_mul_of_nonneg_left hupperPow (le_of_lt hD)
      _ = (2 ^ ρ + 1) * (v / u) ^ (ρ + δ) := by rfl

/-- The upper Potter estimate, in both scale directions, gives a single
integrable-style envelope for a rescaled ratio. The hypothesis `s * u < U`
keeps both arguments inside the interval where the Potter bound is available. -/
theorem exists_potter_envelope_of_uniform_ratio
    {f : ℝ → ℝ} {ρ : ℝ}
    (hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u)
    (huniform : TendstoUniformlyOn
      (fun u r => f (r * u) / f u) (fun r => r ^ ρ)
      (𝓝[>] (0 : ℝ)) (Set.Icc 1 2))
    (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ) :
    ∃ U C : ℝ, 0 < U ∧ 0 < C ∧
      (∀ ⦃u : ℝ⦄, 0 < u → u < U → 0 < f u) ∧
      ∀ ⦃u s : ℝ⦄, 0 < u → u < U → 0 < s → s * u < U →
        f (s * u) / f u ≤ C *
          (s ^ (ρ - δ) + s ^ (ρ + δ)) := by
  obtain ⟨U, hU, hposU, hpot⟩ :=
    exists_potter_bound_of_uniform_ratio hpos huniform hρ hδ hδρ
  let p : ℝ := ρ - δ
  let q : ℝ := ρ + δ
  let c₀ : ℝ := 1 / (2 * 2 ^ p)
  let c₁ : ℝ := 2 * 2 ^ p
  let c₂ : ℝ := 2 ^ ρ + 1
  let C : ℝ := c₁ + c₂
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨U, C, hU, hC, hposU, ?_⟩
  intro u s hu huU hs hsuU
  have hfu : 0 < f u := hposU hu huU
  by_cases hsle : s ≤ 1
  · have hsu : 0 < s * u := mul_pos hs hu
    have hsuLe : s * u ≤ u := by
      calc
        s * u ≤ 1 * u := mul_le_mul_of_nonneg_right hsle hu.le
        _ = u := by ring
    have hpotter := hpot hsu hsuLe huU
    have harg : u / (s * u) = 1 / s := by field_simp [ne_of_gt hs, ne_of_gt hu]
    have hlarge : 0 < c₀ * (1 / s) ^ p := by
      exact mul_pos hc₀ (Real.rpow_pos_of_pos (by positivity) p)
    have hpotterLower : c₀ * (1 / s) ^ p ≤ f u / f (s * u) := by
      simpa [p, c₀, harg] using hpotter.1
    have hratioPos : 0 < f u / f (s * u) :=
      lt_of_lt_of_le hlarge hpotterLower
    have hfsu : 0 < f (s * u) := (div_pos_iff_of_pos_left hfu).mp hratioPos
    have hrecip := one_div_le_one_div_of_le hlarge hpotterLower
    have hratioEq : f (s * u) / f u = 1 / (f u / f (s * u)) := by
      field_simp [ne_of_gt hfu, ne_of_gt hfsu]
    have hpowerEq : 1 / (c₀ * (1 / s) ^ p) = c₁ * s ^ p := by
      rw [show 1 / s = s⁻¹ by simp, Real.inv_rpow hs.le p]
      dsimp [c₀, c₁]
      field_simp
    have hbound : f (s * u) / f u ≤ c₁ * s ^ p := by
      calc
        f (s * u) / f u = 1 / (f u / f (s * u)) := hratioEq
        _ ≤ 1 / (c₀ * (1 / s) ^ p) := hrecip
        _ = c₁ * s ^ p := hpowerEq
    have hsPowP : 0 ≤ s ^ p := (Real.rpow_pos_of_pos hs p).le
    have hsPowQ : 0 ≤ s ^ q := (Real.rpow_pos_of_pos hs q).le
    have hsum : c₁ * s ^ p ≤ C * (s ^ p + s ^ q) := by
      dsimp [C]
      nlinarith [mul_nonneg hc₂.le hsPowP, mul_nonneg hc₁.le hsPowQ]
    exact hbound.trans hsum
  · have honeLt : 1 < s := lt_of_not_ge hsle
    have hle : u ≤ s * u := by
      calc
        u = 1 * u := by ring
        _ ≤ s * u := mul_le_mul_of_nonneg_right honeLt.le hu.le
    have hpotter := hpot hu hle hsuU
    have harg : s * u / u = s := by field_simp [ne_of_gt hu]
    have hbound : f (s * u) / f u ≤ c₂ * s ^ q := by
      simpa [c₂, q, harg] using hpotter.2
    have hsPowP : 0 ≤ s ^ p := (Real.rpow_pos_of_pos hs p).le
    have hsPowQ : 0 ≤ s ^ q := (Real.rpow_pos_of_pos hs q).le
    have hsum : c₂ * s ^ q ≤ C * (s ^ p + s ^ q) := by
      dsimp [C]
      nlinarith [mul_nonneg hc₁.le hsPowP, mul_nonneg hc₂.le hsPowQ]
    exact hbound.trans hsum

/-- A global rescaled-ratio envelope follows from the local Potter envelope
when `f` is bounded and nonnegative away from zero. On scales with `s * u ≥ U`,
the bound on `f` is combined with a fixed reference scale and the upper Potter
estimate. -/
theorem exists_global_potter_envelope_of_uniform_ratio
    {f : ℝ → ℝ} {ρ M : ℝ}
    (hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u)
    (huniform : TendstoUniformlyOn
      (fun u r => f (r * u) / f u) (fun r => r ^ ρ)
      (𝓝[>] (0 : ℝ)) (Set.Icc 1 2))
    (hρ : 0 < ρ) {δ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (hM : 0 ≤ M)
    (hnonneg : ∀ ⦃x : ℝ⦄, 0 ≤ x → 0 ≤ f x)
    (hbounded : ∀ ⦃x : ℝ⦄, 0 ≤ x → f x ≤ M) :
    ∃ U C : ℝ, 0 < U ∧ 0 < C ∧
      (∀ ⦃u : ℝ⦄, 0 < u → u < U → 0 < f u) ∧
      ∀ ⦃u s : ℝ⦄, 0 < u → u < U → 0 < s →
        f (s * u) / f u ≤ C *
          (s ^ (ρ - δ) + s ^ (ρ + δ)) := by
  obtain ⟨U₀, C₀, hU₀, hC₀, hpos₀, henvelope₀⟩ :=
    exists_potter_envelope_of_uniform_ratio hpos huniform hρ hδ hδρ
  let p : ℝ := ρ - δ
  let q : ℝ := ρ + δ
  let v₀ : ℝ := U₀ / 2
  let Ctail : ℝ := M * (2 * C₀ / f v₀) * (v₀ / U₀) ^ q
  let C : ℝ := C₀ + Ctail
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [p, q]; linarith
  have hv₀ : 0 < v₀ := by dsimp [v₀]; linarith
  have hv₀U₀ : v₀ < U₀ := by dsimp [v₀]; linarith
  have hfv₀ : 0 < f v₀ := hpos₀ hv₀ hv₀U₀
  have hCtail : 0 ≤ Ctail := by
    dsimp [Ctail]
    positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hC₀nonneg : 0 ≤ C₀ := le_of_lt hC₀
  refine ⟨v₀, C, hv₀, hC, ?_, ?_⟩
  · intro u hu huV₀
    exact hpos₀ hu (lt_trans huV₀ hv₀U₀)
  · intro u s hu huV₀ hs
    have hfu : 0 < f u := hpos₀ hu (lt_trans huV₀ hv₀U₀)
    by_cases hsmall : s * u < U₀
    · have hlocal := henvelope₀ hu (lt_trans huV₀ hv₀U₀) hs hsmall
      have hsmallConst : C₀ * (s ^ p + s ^ q) ≤ C * (s ^ p + s ^ q) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C]
          exact le_add_of_nonneg_right hCtail
        · positivity
      exact hlocal.trans hsmallConst
    · have hlarge : U₀ ≤ s * u := le_of_not_gt hsmall
      have hratioScale : 1 ≤ v₀ / u := by
        exact (one_le_div₀ hu).2 (le_of_lt huV₀)
      have hsu : 0 < (v₀ / u) * u := by
        rw [div_mul_cancel₀ v₀ hu.ne']
        exact hv₀
      have hsuEq : (v₀ / u) * u = v₀ := div_mul_cancel₀ v₀ hu.ne'
      have href := henvelope₀ hu (lt_trans huV₀ hv₀U₀) (div_pos hv₀ hu)
        (by simpa [hsuEq] using hv₀U₀)
      have hpow : (v₀ / u) ^ p ≤ (v₀ / u) ^ q :=
        Real.rpow_le_rpow_of_exponent_le hratioScale hpq
      have hratioV₀ : f v₀ / f u ≤ 2 * C₀ * (v₀ / u) ^ q := by
        have hsum : (v₀ / u) ^ p + (v₀ / u) ^ q ≤
            2 * (v₀ / u) ^ q := by nlinarith [hpow]
        calc
          f v₀ / f u ≤ C₀ * ((v₀ / u) ^ p + (v₀ / u) ^ q) := by
            simpa [hsuEq, p, q] using href
          _ ≤ C₀ * (2 * (v₀ / u) ^ q) :=
            mul_le_mul_of_nonneg_left hsum hC₀nonneg
          _ = 2 * C₀ * (v₀ / u) ^ q := by ring
      have hrecip : (f u)⁻¹ ≤ (2 * C₀ / f v₀) * (v₀ / u) ^ q := by
        calc
          (f u)⁻¹ = (f v₀ / f u) * (f v₀)⁻¹ := by
            field_simp [ne_of_gt hfu, ne_of_gt hfv₀]
          _ ≤ (2 * C₀ * (v₀ / u) ^ q) * (f v₀)⁻¹ :=
            mul_le_mul_of_nonneg_right hratioV₀ (inv_nonneg.mpr hfv₀.le)
          _ = (2 * C₀ / f v₀) * (v₀ / u) ^ q := by ring
      have hfuNonneg : 0 ≤ (f u)⁻¹ := inv_nonneg.mpr hfu.le
      have hfsuNonneg : 0 ≤ f (s * u) := hnonneg (mul_nonneg hs.le hu.le)
      have hfsuBound : f (s * u) ≤ M := hbounded (mul_nonneg hs.le hu.le)
      have hratioTail : f (s * u) / f u ≤
          M * (2 * C₀ / f v₀) * (v₀ / U₀) ^ q * s ^ q := by
        have hratioEq : f (s * u) / f u = f (s * u) * (f u)⁻¹ := by
          rw [div_eq_mul_inv]
        rw [hratioEq]
        have hmulRecip : f (s * u) * (f u)⁻¹ ≤
            f (s * u) * ((2 * C₀ / f v₀) * (v₀ / u) ^ q) :=
          mul_le_mul_of_nonneg_left hrecip hfsuNonneg
        have hmulBound : f (s * u) * ((2 * C₀ / f v₀) * (v₀ / u) ^ q) ≤
            M * ((2 * C₀ / f v₀) * (v₀ / u) ^ q) :=
          mul_le_mul_of_nonneg_right hfsuBound (by positivity)
        have hscale : v₀ / u ≤ (v₀ / U₀) * s := by
          have hUdiv : U₀ / u ≤ s := (div_le_iff₀ hu).2 (by nlinarith [hlarge])
          calc
            v₀ / u = (v₀ / U₀) * (U₀ / u) := by field_simp [ne_of_gt hU₀, ne_of_gt hu]
            _ ≤ (v₀ / U₀) * s :=
              mul_le_mul_of_nonneg_left hUdiv (div_nonneg (le_of_lt hv₀) hU₀.le)
        have hscalePow : (v₀ / u) ^ q ≤ ((v₀ / U₀) * s) ^ q :=
          Real.rpow_le_rpow (by positivity) hscale hq.le
        have hscalePow' : ((v₀ / U₀) * s) ^ q = (v₀ / U₀) ^ q * s ^ q :=
          Real.mul_rpow (by positivity) hs.le
        calc
          f (s * u) / f u ≤ M * ((2 * C₀ / f v₀) * (v₀ / u) ^ q) :=
            hmulRecip.trans hmulBound
          _ ≤ M * ((2 * C₀ / f v₀) * (((v₀ / U₀) * s) ^ q)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hscalePow (by positivity)
            · exact hM
          _ = M * (2 * C₀ / f v₀) * (v₀ / U₀) ^ q * s ^ q := by
            rw [hscalePow']
            ring
      have htailSum : Ctail * s ^ q ≤ C * (s ^ p + s ^ q) := by
        have hsp : 0 ≤ s ^ p := (Real.rpow_pos_of_pos hs p).le
        have hsq : 0 ≤ s ^ q := (Real.rpow_pos_of_pos hs q).le
        dsimp [C]
        have hqsum : s ^ q ≤ s ^ p + s ^ q := by linarith
        calc
          Ctail * s ^ q ≤ Ctail * (s ^ p + s ^ q) :=
            mul_le_mul_of_nonneg_left hqsum hCtail
          _ ≤ (C₀ + Ctail) * (s ^ p + s ^ q) := by
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hratioTail' : f (s * u) / f u ≤ Ctail * s ^ q := by
        simpa [Ctail, mul_assoc, mul_left_comm, mul_comm] using hratioTail
      exact hratioTail'.trans htailSum

end Asymptotics.IsRegularlyVaryingAtZero

end
