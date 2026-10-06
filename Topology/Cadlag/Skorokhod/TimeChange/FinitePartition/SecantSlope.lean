/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.FinitePartition.Homeomorph
public import Topology.Cadlag.Skorokhod.TimeChange.LogDistortion

/-!
# Secant slopes of finite-partition time changes

Close corresponding knots and a positive minimum target-cell length give a
uniform bound on all secant slopes of the matching piecewise-affine clock.
-/

@[expose] public section

namespace Skorokhod.TimeChange.FinitePartition

private theorem ofMatchingPartitions_apply_points {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (i : Fin (n + 1)) :
    (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict) (source i) = target i := by
  by_cases hi : i.val < n
  · let j : Fin n := ⟨i.val, hi⟩
    have hij : j.castSucc = i := by
      apply Fin.ext
      rfl
    rw [← hij]
    exact map_apply_cellStart hn source target hsourceFirst hsourceLast hsourceStrict
      htargetStrict j
  · have hiLast : i = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst i
    have hs : source (Fin.last n) = ⊤ := by
      simpa [Fin.last] using hsourceLast
    have ht : target (Fin.last n) = ⊤ := by
      simpa [Fin.last] using htargetLast
    rw [hs, ht, TimeChange.apply_top]

private theorem map_eq_affine_on_cell {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (i : Fin n) (x : unitInterval)
    (hleft : source i.castSucc ≤ x) (hright : x ≤ source i.succ) :
    ((map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict x :
      unitInterval) : ℝ) =
      affineInterpolate (source i.castSucc) (source i.succ)
        (target i.castSucc) (target i.succ) x := by
  have hgap : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
    exact_mod_cast hsourceStrict i.castSucc_lt_succ
  by_cases hx : x < source i.succ
  · let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict

    have hindex : p.index x = i :=
      p.index_eq_of_cell i x hleft (Or.inl hx)
    rw [coe_map, interpolationValue_eq_affine hn source target hsourceFirst hsourceLast
      hsourceStrict x i hindex]
  · have hx' : x = source i.succ := le_antisymm hright (not_lt.mp hx)
    rw [hx']
    change ((ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict) (source i.succ) : ℝ) = _
    rw [ofMatchingPartitions_apply_points hn source target hsourceFirst hsourceLast
      hsourceStrict htargetFirst htargetLast htargetStrict i.succ]
    exact (affineInterpolate_right hgap).symm

private theorem secantSlope_ofMatchingPartitions_on_cell {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (i : Fin n) {s t : unitInterval}
    (hst : s < t) (hleft : source i.castSucc ≤ s)
    (hright : t ≤ source i.succ) :
    (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict).secantSlope s t =
      ((target i.succ : ℝ) - (target i.castSucc : ℝ)) /
        ((source i.succ : ℝ) - (source i.castSucc : ℝ)) := by
  have hslope := map_eq_affine_on_cell hn source target hsourceFirst hsourceLast
    hsourceStrict htargetFirst htargetLast htargetStrict i s hleft
    (le_trans (Subtype.coe_le_coe.mpr hst.le) hright)
  have htlope := map_eq_affine_on_cell hn source target hsourceFirst hsourceLast
    hsourceStrict htargetFirst htargetLast htargetStrict i t
    (le_trans hleft (Subtype.coe_le_coe.mpr hst.le)) hright
  have hsourceGap : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
    exact_mod_cast hsourceStrict i.castSucc_lt_succ
  have htargetGap : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
    exact_mod_cast htargetStrict i.castSucc_lt_succ
  have hdenom : (source i.succ : ℝ) - (source i.castSucc : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hsourceGap)
  have htime : (t : ℝ) - (s : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (by exact_mod_cast hst))
  change ((((map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t :
      unitInterval) : ℝ) -
      ((map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict s :
        unitInterval) : ℝ)) / ((t : ℝ) - (s : ℝ))) = _
  rw [hslope, htlope]
  unfold affineInterpolate
  field_simp [hdenom, htime]
  ring_nf

private theorem secantSlope_mem_band_ofMatchingPartitions_on_cell {n : ℕ}
    (hn : 0 < n) (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (mesh δ : ℝ)
    (hmesh : 0 < mesh) (hδ : 0 ≤ δ) (hδsmall : δ < mesh / 8)
    (hgap : ∀ i : Fin n, mesh ≤ dist (target i.castSucc) (target i.succ))
    (hpoints : ∀ i : Fin (n + 1), dist (source i) (target i) ≤ δ)
    (i : Fin n) {s t : unitInterval} (hst : s < t)
    (hleft : source i.castSucc ≤ s) (hright : t ≤ source i.succ) :
    |(ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict).secantSlope s t - 1| ≤ 4 * δ / mesh := by
  have hsourceOrder : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
    exact_mod_cast hsourceStrict i.castSucc_lt_succ
  have htargetOrder : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
    exact_mod_cast htargetStrict i.castSucc_lt_succ
  let sg := (source i.succ : ℝ) - (source i.castSucc : ℝ)
  let tg := (target i.succ : ℝ) - (target i.castSucc : ℝ)
  have hsg : 0 < sg := by dsimp [sg]; linarith
  have htg : 0 < tg := by dsimp [tg]; linarith
  have htargetGap : mesh ≤ tg := by
    have h := hgap i
    dsimp [tg]
    simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith :
      (target i.castSucc : ℝ) - (target i.succ : ℝ) ≤ 0)] using h
  have hdisp_left : |(source i.castSucc : ℝ) - (target i.castSucc : ℝ)| ≤ δ := by
    have h := hpoints i.castSucc
    simpa [Subtype.dist_eq, Real.dist_eq] using h
  have hdisp_right : |(source i.succ : ℝ) - (target i.succ : ℝ)| ≤ δ := by
    have h := hpoints i.succ
    simpa [Subtype.dist_eq, Real.dist_eq] using h
  have hgapdiff : |tg - sg| ≤ 2 * δ := by
    have hformula : tg - sg =
        ((target i.succ : ℝ) - (source i.succ : ℝ)) -
          ((target i.castSucc : ℝ) - (source i.castSucc : ℝ)) := by
      dsimp [tg, sg]
      ring
    rw [hformula]
    calc
      _ ≤ |(target i.succ : ℝ) - (source i.succ : ℝ)| +
          |(target i.castSucc : ℝ) - (source i.castSucc : ℝ)| := abs_sub _ _
      _ ≤ δ + δ := add_le_add (by simpa [abs_sub_comm] using hdisp_right)
          (by simpa [abs_sub_comm] using hdisp_left)
      _ = 2 * δ := by ring
  have hsg_lower : mesh - 2 * δ ≤ sg := by
    have h := (abs_le.mp hgapdiff).2
    linarith [htargetGap]
  have hsg_half : mesh / 2 ≤ sg := by
    have : 2 * δ ≤ mesh / 2 := by linarith [hδsmall]
    linarith
  have hratio : tg / sg =
      (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
        htargetFirst htargetLast htargetStrict).secantSlope s t := by
    rw [secantSlope_ofMatchingPartitions_on_cell hn source target hsourceFirst hsourceLast
      hsourceStrict htargetFirst htargetLast htargetStrict i hst hleft hright]
  have hratio_diff : tg / sg - 1 = (tg - sg) / sg := by
    field_simp [ne_of_gt hsg]
  rw [← hratio, hratio_diff, abs_div, abs_of_pos hsg]
  calc
    |tg - sg| / sg ≤ (2 * δ) / sg :=
      div_le_div_of_nonneg_right hgapdiff hsg.le
    _ ≤ 4 * δ / mesh := by
      apply (div_le_div_iff₀ hsg hmesh).2
      nlinarith [hsg_half, hδ]

private theorem matching_source_gap_lower {n : ℕ}
    (source target : Fin (n + 1) → unitInterval)
    (hsourceStrict : StrictMono source)
    (htargetStrict : StrictMono target) (mesh δ : ℝ)
    (hδsmall : δ < mesh / 8)
    (hgap : ∀ i : Fin n, mesh ≤ dist (target i.castSucc) (target i.succ))
    (hpoints : ∀ i : Fin (n + 1), dist (source i) (target i) ≤ δ)
    (i : Fin n) :
    3 * mesh / 4 ≤ (source i.succ : ℝ) - (source i.castSucc : ℝ) := by
  have hsourceOrder : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
    exact_mod_cast hsourceStrict i.castSucc_lt_succ
  have htargetOrder : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
    exact_mod_cast htargetStrict i.castSucc_lt_succ
  let sg := (source i.succ : ℝ) - (source i.castSucc : ℝ)
  let tg := (target i.succ : ℝ) - (target i.castSucc : ℝ)
  have htargetGap : mesh ≤ tg := by
    have h := hgap i
    dsimp [tg]
    simpa [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith :
      (target i.castSucc : ℝ) - (target i.succ : ℝ) ≤ 0)] using h
  have hdisp_left : |(source i.castSucc : ℝ) - (target i.castSucc : ℝ)| ≤ δ := by
    simpa [Subtype.dist_eq, Real.dist_eq] using hpoints i.castSucc
  have hdisp_right : |(source i.succ : ℝ) - (target i.succ : ℝ)| ≤ δ := by
    simpa [Subtype.dist_eq, Real.dist_eq] using hpoints i.succ
  have hgapdiff : |tg - sg| ≤ 2 * δ := by
    have hformula : tg - sg =
        ((target i.succ : ℝ) - (source i.succ : ℝ)) -
          ((target i.castSucc : ℝ) - (source i.castSucc : ℝ)) := by
      dsimp [tg, sg]
      ring
    rw [hformula]
    calc
      _ ≤ |(target i.succ : ℝ) - (source i.succ : ℝ)| +
          |(target i.castSucc : ℝ) - (source i.castSucc : ℝ)| := abs_sub _ _
      _ ≤ δ + δ := add_le_add (by simpa [abs_sub_comm] using hdisp_right)
          (by simpa [abs_sub_comm] using hdisp_left)
      _ = 2 * δ := by ring
  have hlow : mesh - 2 * δ ≤ sg := by
    have h := (abs_le.mp hgapdiff).2
    dsimp [sg, tg] at h ⊢
    linarith [htargetGap]
  have hδbound : 2 * δ ≤ mesh / 4 := by linarith [hδsmall]
  linarith

private theorem oscillationPartition_index_lt_right
    (partition : OscillationPartition) {x : unitInterval} (hx : x ≠ ⊤) :
    x < partition.points (partition.index x).succ := by
  rcases partition.index_upper x with h | hlast
  · exact h
  · have hindex : (partition.index x).succ = Fin.last partition.size := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    have hpoint : partition.points (partition.index x).succ = ⊤ := by
      rw [hindex]
      simpa [Fin.last] using partition.last
    rw [hpoint]
    exact lt_top_iff_ne_top.mpr hx

private theorem oscillationPartition_index_le_right
    (partition : OscillationPartition) (x : unitInterval) :
    x ≤ partition.points (partition.index x).succ := by
  rcases partition.index_upper x with h | hlast
  · exact h.le
  · have hindex : (partition.index x).succ = Fin.last partition.size := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    have hpoint : partition.points (partition.index x).succ = ⊤ := by
      rw [hindex]
      simpa [Fin.last] using partition.last
    rw [hpoint]
    exact le_top

private theorem abs_weighted_secantSlope_minus_one_le {x y r₁ r₂ q : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (h₁ : |r₁ - 1| ≤ q) (h₂ : |r₂ - 1| ≤ q) :
    |(r₁ * x + r₂ * y) / (x + y) - 1| ≤ q := by
  have h₁' := abs_le.mp h₁
  have h₂' := abs_le.mp h₂
  have hden : 0 < x + y := add_pos hx hy
  have hlower : (1 - q) * (x + y) ≤ r₁ * x + r₂ * y := by
    nlinarith [mul_le_mul_of_nonneg_right h₁'.1 hx.le,
      mul_le_mul_of_nonneg_right h₂'.1 hy.le]
  have hupper : r₁ * x + r₂ * y ≤ (1 + q) * (x + y) := by
    nlinarith [mul_le_mul_of_nonneg_right h₁'.2 hx.le,
      mul_le_mul_of_nonneg_right h₂'.2 hy.le]
  have hratioLow : 1 - q ≤ (r₁ * x + r₂ * y) / (x + y) :=
    (le_div_iff₀ hden).2 hlower
  have hratioHigh : (r₁ * x + r₂ * y) / (x + y) ≤ 1 + q :=
    (div_le_iff₀ hden).2 hupper
  rw [abs_le]
  constructor <;> linarith

private theorem matching_map_secantSlope_mem_band {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (mesh δ : ℝ)
    (hmesh : 0 < mesh) (hδ : 0 ≤ δ) (hδsmall : δ < mesh / 8)
    (hsourceGap : ∀ i : Fin n,
      3 * mesh / 4 ≤ (source i.succ : ℝ) - (source i.castSucc : ℝ))
    (hgap : ∀ i : Fin n, mesh ≤ dist (target i.castSucc) (target i.succ))
    (hpoints : ∀ i : Fin (n + 1), dist (source i) (target i) ≤ δ)
    {s t : unitInterval} (hst : s < t) :
    |(ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict).secantSlope s t - 1| ≤ 4 * δ / mesh := by
  let τ := ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
    htargetFirst htargetLast htargetStrict
  let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict
  have hpPoints : p.points = source := rfl
  let i := p.index s
  let j := p.index t
  have hij : i ≤ j := p.index_monotone hst.le
  have hsTop : s ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hst le_top)
  have hsRight : s < source i.succ := by
    have h := oscillationPartition_index_lt_right p hsTop
    rw [hpPoints] at h
    exact h
  have htRight : t ≤ source j.succ := by
    have h := oscillationPartition_index_le_right p t
    rw [hpPoints] at h
    exact h
  have hsourceDisportion : τ.distortion ≤ δ :=
    ofMatchingPartitions_distortion_le hn source target hsourceFirst hsourceLast
      hsourceStrict htargetFirst htargetLast htargetStrict δ hpoints
  have hsourceAt (x : unitInterval) : |(τ x : ℝ) - (x : ℝ)| ≤ δ := by
    have h := τ.dist_apply_le_distortion x
    have h' : dist (τ x) x ≤ δ := h.trans hsourceDisportion
    simpa [Subtype.dist_eq, Real.dist_eq] using h'
  have hsecant :
      |τ.secantSlope s t - 1| ≤ 4 * δ / mesh := by
    by_cases hlong : mesh / 2 ≤ (t : ℝ) - (s : ℝ)
    · have htime : 0 < (t : ℝ) - (s : ℝ) :=
        sub_pos.mpr (by exact_mod_cast hst)
      have hdisp : |((τ t : ℝ) - (τ s : ℝ)) - ((t : ℝ) - (s : ℝ))| ≤ 2 * δ := by
        have hformula :
            ((τ t : ℝ) - (τ s : ℝ)) - ((t : ℝ) - (s : ℝ)) =
              ((τ t : ℝ) - (t : ℝ)) - ((τ s : ℝ) - (s : ℝ)) := by ring
        rw [hformula]
        calc
          _ ≤ |(τ t : ℝ) - (t : ℝ)| + |(τ s : ℝ) - (s : ℝ)| := by
            simpa [abs_sub_comm] using abs_sub_le ((τ t : ℝ) - (t : ℝ)) 0
              ((τ s : ℝ) - (s : ℝ))
          _ ≤ δ + δ := add_le_add (hsourceAt t)
            (by simpa [abs_sub_comm] using hsourceAt s)
          _ = 2 * δ := by ring
      have hratio : τ.secantSlope s t - 1 =
          (((τ t : ℝ) - (τ s : ℝ)) - ((t : ℝ) - (s : ℝ))) /
            ((t : ℝ) - (s : ℝ)) := by
        unfold TimeChange.secantSlope
        field_simp [ne_of_gt htime]
      rw [hratio, abs_div, abs_of_pos htime]
      calc
        _ ≤ (2 * δ) / ((t : ℝ) - (s : ℝ)) :=
          div_le_div_of_nonneg_right hdisp htime.le
        _ ≤ 4 * δ / mesh := by
          apply (div_le_div_iff₀ htime hmesh).2
          nlinarith [hlong, hδ]
    · have hshort : (t : ℝ) - (s : ℝ) < mesh / 2 := lt_of_not_ge hlong
      by_cases hsame : i = j
      · have hindexT : p.index t = i := by simpa [j] using hsame.symm
        have hleft : source i.castSucc ≤ s := by
          have h := p.index_lower s
          rw [hpPoints] at h
          simpa [i] using h
        have hright : t ≤ source i.succ := by
          have h := oscillationPartition_index_le_right p t
          rw [hpPoints, hindexT] at h
          exact h
        exact secantSlope_mem_band_ofMatchingPartitions_on_cell hn source target
          hsourceFirst hsourceLast hsourceStrict htargetFirst htargetLast htargetStrict
          mesh δ hmesh hδ hδsmall hgap hpoints i hst hleft hright
      · have hijlt : i < j := lt_of_le_of_ne hij (fun hji => hsame hji)
        have hconsecutive : j.val = i.val + 1 := by
          by_contra hnot
          have hfar : i.val + 2 ≤ j.val := by omega
          have hpSize : p.size = n := rfl
          let k : Fin n := ⟨i.val + 1, by omega⟩
          have hkleft : k.castSucc = i.succ := by
            apply Fin.ext
            rfl
          have hknext : k.succ ≤ j.castSucc := by
            apply Fin.le_iff_val_le_val.mpr
            simp [k]
            omega
          have hsourceOrd : source k.succ ≤ source j.castSucc :=
            hsourceStrict.monotone hknext
          have htimegap : 3 * mesh / 4 ≤ (t : ℝ) - (s : ℝ) := by
            have hsourceStart : (source k.succ : ℝ) ≤ t := by
              have h := p.index_lower t
              rw [hpPoints] at h
              exact_mod_cast le_trans hsourceOrd h
            have hsourceEnd : (s : ℝ) < (source k.castSucc : ℝ) := by
              rw [hkleft]
              exact_mod_cast hsRight
            have hgap' := hsourceGap k
            linarith
          linarith [hshort, hmesh]
        have hconsecutiveFin : i.succ = j.castSucc := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        let r := source i.succ
        have hrle : r ≤ t := by
          dsimp [r]
          rw [hconsecutiveFin]
          have h := p.index_lower t
          rw [hpPoints] at h
          exact h
        have hslt : s < r := by
          dsimp [r]
          exact hsRight
        by_cases hrt : r = t
        · have hleft : source i.castSucc ≤ s := by
            have h := p.index_lower s
            rw [hpPoints] at h
            simpa [i] using h
          have hright : t ≤ source i.succ := by simpa [r] using hrt.ge
          exact secantSlope_mem_band_ofMatchingPartitions_on_cell hn source target
            hsourceFirst hsourceLast hsourceStrict htargetFirst htargetLast htargetStrict
            mesh δ hmesh hδ hδsmall hgap hpoints i hst hleft hright
        · have hrt' : r < t := lt_of_le_of_ne hrle hrt
          have hleftS : source i.castSucc ≤ s := by
            have h := p.index_lower s
            rw [hpPoints] at h
            simpa [i] using h
          have hfirst := secantSlope_mem_band_ofMatchingPartitions_on_cell hn source target
            hsourceFirst hsourceLast hsourceStrict htargetFirst htargetLast htargetStrict
            mesh δ hmesh hδ hδsmall hgap hpoints i hslt hleftS (le_of_eq rfl)
          have hleftT : source j.castSucc ≤ r := by
            rw [← hconsecutiveFin]
          have hrightT : t ≤ source j.succ := htRight
          have hsecond := secantSlope_mem_band_ofMatchingPartitions_on_cell hn source target
            hsourceFirst hsourceLast hsourceStrict htargetFirst htargetLast htargetStrict
            mesh δ hmesh hδ hδsmall hgap hpoints j hrt' hleftT hrightT
          let x := (r : ℝ) - (s : ℝ)
          let y := (t : ℝ) - (r : ℝ)
          let r₁ := τ.secantSlope s r
          let r₂ := τ.secantSlope r t
          have hx : 0 < x := by
            dsimp [x]
            exact sub_pos.mpr (by exact_mod_cast hslt)
          have hy : 0 < y := by
            dsimp [y]
            exact sub_pos.mpr (by exact_mod_cast hrt')
          have hx' : (r : ℝ) - (s : ℝ) ≠ 0 :=
            ne_of_gt (sub_pos.mpr (by exact_mod_cast hslt))
          have hy' : (t : ℝ) - (r : ℝ) ≠ 0 :=
            ne_of_gt (sub_pos.mpr (by exact_mod_cast hrt'))
          have hr₁ : |r₁ - 1| ≤ 4 * δ / mesh := by simpa [r₁] using hfirst
          have hr₂ : |r₂ - 1| ≤ 4 * δ / mesh := by simpa [r₂] using hsecond
          have hmapAdd : (τ t : ℝ) - (τ s : ℝ) =
              ((τ r : ℝ) - (τ s : ℝ)) + ((τ t : ℝ) - (τ r : ℝ)) := by ring
          have htimeAdd : (t : ℝ) - (s : ℝ) = x + y := by
            dsimp [x, y]
            ring
          have hfirstMul : r₁ * x = (τ r : ℝ) - (τ s : ℝ) := by
            dsimp [r₁, x]
            unfold TimeChange.secantSlope
            field_simp [hx']
          have hsecondMul : r₂ * y = (τ t : ℝ) - (τ r : ℝ) := by
            dsimp [r₂, y]
            unfold TimeChange.secantSlope
            field_simp [hy']
          have hcombined : τ.secantSlope s t =
              (r₁ * x + r₂ * y) / (x + y) := by
            unfold TimeChange.secantSlope
            rw [hmapAdd, htimeAdd, ← hfirstMul, ← hsecondMul]
          rw [hcombined]
          exact abs_weighted_secantSlope_minus_one_le hx hy hr₁ hr₂
  simpa [τ] using hsecant

/-- Corresponding close knots give uniformly controlled secant slopes for the
piecewise-affine map matching two finite partitions. -/
theorem ofMatchingPartitions_secantSlope_mem_Icc {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (mesh δ : ℝ)
    (hmesh : 0 < mesh) (hδ : 0 ≤ δ) (hδsmall : δ < mesh / 8)
    (hgap : ∀ i : Fin n, mesh ≤ dist (target i.castSucc) (target i.succ))
    (hpoints : ∀ i : Fin (n + 1), dist (source i) (target i) ≤ δ)
    (p : TimeChange.SecantPair) :
    1 - 4 * δ / mesh ≤
        (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
          htargetFirst htargetLast htargetStrict).secantSlope p.1.1 p.1.2 ∧
      (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
        htargetFirst htargetLast htargetStrict).secantSlope p.1.1 p.1.2 ≤
          1 + 4 * δ / mesh := by
  have hsourceGap : ∀ i : Fin n,
      3 * mesh / 4 ≤ (source i.succ : ℝ) - (source i.castSucc : ℝ) := by
    intro i
    exact matching_source_gap_lower source target hsourceStrict htargetStrict mesh δ
      hδsmall hgap hpoints i
  have h := matching_map_secantSlope_mem_band hn source target hsourceFirst hsourceLast
    hsourceStrict htargetFirst htargetLast htargetStrict mesh δ hmesh hδ hδsmall
    hsourceGap hgap hpoints p.2
  have h' := abs_le.mp h
  constructor <;> linarith

end Skorokhod.TimeChange.FinitePartition

end
