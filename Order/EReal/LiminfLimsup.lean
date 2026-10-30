/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended-real limits of real-valued functions

This module gives order translation and perturbation rules for limsup and
liminf of real-valued functions viewed in `EReal`. The index type and filter
are arbitrary. These results are independent of probability and Kingman's
theorem.

## Public declarations

The module exposes the following declarations:

- `EReal.addCoeOrderIso`: translation $x\mapsto x+c$ is an order isomorphism.
- `EReal.limsup_add_coe` and `EReal.liminf_add_coe`:
  $\limsup (\uparrow u+c)=\limsup(\uparrow u)+c$ and the analogous liminf identity.
- `EReal.liminf_coe_le_of_sub_tendsto_zero`:
  $a-b\to0$ implies $\liminf\uparrow b\le\liminf\uparrow a$.
- `EReal.liminf_coe_eq_of_sub_tendsto_zero` and
  `EReal.limsup_coe_eq_of_sub_tendsto_zero`: if $u-v\to0$, the corresponding
  extended-real limits of $\uparrow u$ and $\uparrow v$ agree.
- `EReal.limsup_add_tendsto_coe` and `EReal.liminf_add_tendsto_coe`:
  if $s\to\sigma\in\mathbb R$, then the limit of $\uparrow(b+s)$ is the
  limit of $\uparrow b$ plus $\uparrow\sigma$.
- `EReal.liminf_coe_le_liminf_coe_mul_of_nonpos` and
  `EReal.limsup_coe_le_limsup_coe_mul_of_nonpos`: if $z\le0$ and $c\to1$, the corresponding
  extended-real limit of $\uparrow z$ is at most that of $\uparrow(cz)$.
- `EReal.limsup_coe_mul_le_limsup_coe_of_nonpos`: if $z\le0$ and $c\to1$, then
  $\limsup\uparrow(cz)\le\limsup\uparrow z$.
-/

@[expose] public section

open Filter Topology

namespace EReal

/-- Translation by a finite real number is an order isomorphism of `EReal`. -/
noncomputable def addCoeOrderIso (c : ℝ) : EReal ≃o EReal where
  toFun y := y + (c : EReal)
  invFun y := y - (c : EReal)
  left_inv y := by
    simp only
    rw [EReal.add_sub_cancel_right]
  right_inv y := by
    simp only
    rw [EReal.sub_add_cancel]
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_fn_mk]
    exact (EReal.addLECancellable_coe c).add_le_add_iff_right

/-- Adding a finite real constant commutes with `limsup` in `EReal`. -/
theorem limsup_add_coe {ι : Type*} {l : Filter ι} [NeBot l]
    (u : ι → ℝ) (c : ℝ) :
    Filter.limsup (fun i => ((u i : ℝ) : EReal) + (c : EReal)) l
      = Filter.limsup (fun i => ((u i : ℝ) : EReal)) l + (c : EReal) := by
  have h := (addCoeOrderIso c).limsup_apply
    (u := fun i => ((u i : ℝ) : EReal)) (f := l)
    (by isBoundedDefault) (by isBoundedDefault)
    (by isBoundedDefault) (by isBoundedDefault)
  simp only [addCoeOrderIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk] at h
  exact h.symm

/-- Adding a finite real constant commutes with `liminf` in `EReal`. -/
theorem liminf_add_coe {ι : Type*} {l : Filter ι} [NeBot l]
    (u : ι → ℝ) (c : ℝ) :
    Filter.liminf (fun i => ((u i : ℝ) : EReal) + (c : EReal)) l
      = Filter.liminf (fun i => ((u i : ℝ) : EReal)) l + (c : EReal) := by
  have h := (addCoeOrderIso c).liminf_apply
    (u := fun i => ((u i : ℝ) : EReal)) (f := l)
    (by isBoundedDefault) (by isBoundedDefault)
    (by isBoundedDefault) (by isBoundedDefault)
  simp only [addCoeOrderIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk] at h
  exact h.symm

/-- If `a - b` tends to zero, the `EReal` liminf of `b` is at most that of `a`.
No boundedness assumption on either real-valued function is needed. -/
theorem liminf_coe_le_of_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    [NeBot l] {a b : ι → ℝ}
    (hab : Tendsto (fun i => a i - b i) l (𝓝 0)) :
    Filter.liminf (fun i => ((b i : ℝ) : EReal)) l
      ≤ Filter.liminf (fun i => ((a i : ℝ) : EReal)) l := by
  have hetend : Tendsto (fun i => ((a i - b i : ℝ) : EReal)) l
      (𝓝 ((0 : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hab
  have heliminf : Filter.liminf (fun i => ((a i - b i : ℝ) : EReal)) l = 0 := by
    rw [hetend.liminf_eq]
    norm_num
  have hsplit : (fun i => ((a i : ℝ) : EReal))
      = (fun i => ((b i : ℝ) : EReal))
        + (fun i => ((a i - b i : ℝ) : EReal)) := by
    funext i
    simp only [Pi.add_apply]
    rw [← EReal.coe_add]
    congr 1
    ring
  have hadd := EReal.le_liminf_add (f := l)
    (u := fun i => ((b i : ℝ) : EReal))
    (v := fun i => ((a i - b i : ℝ) : EReal))
  rw [heliminf, add_zero] at hadd
  rwa [hsplit]

/-- If the difference of two real-valued functions tends to zero, their
`EReal` liminfs agree. -/
theorem liminf_coe_eq_of_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    [NeBot l] {u v : ι → ℝ}
    (h : Tendsto (fun i => u i - v i) l (𝓝 0)) :
    Filter.liminf (fun i => ((u i : ℝ) : EReal)) l
      = Filter.liminf (fun i => ((v i : ℝ) : EReal)) l := by
  refine le_antisymm ?_ (liminf_coe_le_of_sub_tendsto_zero h)
  apply liminf_coe_le_of_sub_tendsto_zero
  have hneg : (fun i => v i - u i) = fun i => -(u i - v i) := by
    funext i
    ring
  rw [hneg]
  simpa using h.neg

/-- If the difference of two real-valued functions tends to zero, their
`EReal` limsups agree. -/
theorem limsup_coe_eq_of_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    [NeBot l] {u v : ι → ℝ}
    (h : Tendsto (fun i => u i - v i) l (𝓝 0)) :
    Filter.limsup (fun i => ((u i : ℝ) : EReal)) l
      = Filter.limsup (fun i => ((v i : ℝ) : EReal)) l := by
  have hneg : Tendsto (fun i => (-u i) - (-v i)) l (𝓝 0) := by
    have hfun : (fun i => (-u i) - (-v i)) = fun i => -(u i - v i) := by
      funext i
      ring
    rw [hfun]
    simpa using h.neg
  have hliminf := liminf_coe_eq_of_sub_tendsto_zero hneg
  have hdual : ∀ w : ι → ℝ,
      Filter.limsup (fun i => ((w i : ℝ) : EReal)) l
        = -Filter.liminf (fun i => ((-w i : ℝ) : EReal)) l := by
    intro w
    have hfun : (fun i => ((-w i : ℝ) : EReal))
        = -(fun i => ((w i : ℝ) : EReal)) := by
      funext i
      rw [Pi.neg_apply, EReal.coe_neg]
    rw [hfun, EReal.liminf_neg, neg_neg]
  rw [hdual u, hdual v, hliminf]

/-- If `s` tends to `σ`, adding `s` to a real-valued function shifts its
`EReal` limsup by `↑σ`. -/
theorem limsup_add_tendsto_coe {ι : Type*} {l : Filter ι}
    [NeBot l] {b s : ι → ℝ} {σ : ℝ}
    (hs : Tendsto s l (𝓝 σ)) :
    Filter.limsup (fun i => ((b i + s i : ℝ) : EReal)) l
      = Filter.limsup (fun i => ((b i : ℝ) : EReal)) l + (σ : EReal) := by
  have hperturb : Tendsto (fun i => (b i + s i) - (b i + σ)) l (𝓝 0) := by
    have hfun : (fun i => (b i + s i) - (b i + σ)) = fun i => s i - σ := by
      funext i
      ring
    rw [hfun]
    have hs' := hs.sub (tendsto_const_nhds (x := σ))
    have hzero : σ - σ = 0 := by ring
    rw [← hzero]
    exact hs'
  rw [limsup_coe_eq_of_sub_tendsto_zero hperturb]
  have hsplit : (fun i => ((b i + σ : ℝ) : EReal))
      = fun i => ((b i : ℝ) : EReal) + (σ : EReal) := by
    funext i
    rw [EReal.coe_add]
  rw [hsplit, limsup_add_coe]

/-- If `s` tends to `σ`, adding `s` to a real-valued function shifts its
`EReal` liminf by `↑σ`. -/
theorem liminf_add_tendsto_coe {ι : Type*} {l : Filter ι}
    [NeBot l] {b s : ι → ℝ} {σ : ℝ}
    (hs : Tendsto s l (𝓝 σ)) :
    Filter.liminf (fun i => ((b i + s i : ℝ) : EReal)) l
      = Filter.liminf (fun i => ((b i : ℝ) : EReal)) l + (σ : EReal) := by
  have hperturb : Tendsto (fun i => (b i + s i) - (b i + σ)) l (𝓝 0) := by
    have hfun : (fun i => (b i + s i) - (b i + σ)) = fun i => s i - σ := by
      funext i
      ring
    rw [hfun]
    have hs' := hs.sub (tendsto_const_nhds (x := σ))
    have hzero : σ - σ = 0 := by ring
    rw [← hzero]
    exact hs'
  rw [liminf_coe_eq_of_sub_tendsto_zero hperturb]
  have hsplit : (fun i => ((b i + σ : ℝ) : EReal))
      = fun i => ((b i : ℝ) : EReal) + (σ : EReal) := by
    funext i
    rw [EReal.coe_add]
  rw [hsplit, liminf_add_coe]

/-- **Liminf under an asymptotically unit factor.** For functions `c, z : ι → ℝ` indexed by any
nontrivial filter, if `z ≤ 0` pointwise and `c → 1`, then
`liminf ↑z ≤ liminf ↑(c * z)`. The proof bounds `c` between `1 ± ε`, applies the constant-factor
`EReal` liminf law, and lets `ε` tend to zero. -/
theorem liminf_coe_le_liminf_coe_mul_of_nonpos {ι : Type*} {l : Filter ι} [NeBot l]
    {c z : ι → ℝ} (hz : ∀ i, z i ≤ 0)
    (hctend : Tendsto c l (𝓝 1)) :
    Filter.liminf (fun n => ((z n : ℝ) : EReal)) l
      ≤ Filter.liminf (fun n => ((c n * z n : ℝ) : EReal)) l := by
  set Lz : EReal := Filter.liminf (fun n => ((z n : ℝ) : EReal)) l with hLz
  set Lcz : EReal := Filter.liminf (fun n => ((c n * z n : ℝ) : EReal)) l with hLcz
  -- `Lz ≤ 0`.
  have hLz0 : Lz ≤ 0 := by
    rw [hLz]
    refine le_trans (Filter.liminf_le_liminf (Eventually.of_forall fun n =>
      (EReal.coe_le_coe_iff.2 (hz n) : ((z n : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)))) ?_
    simp [Filter.liminf_const]
  -- For every real `ε > 0`: `↑(1+ε) * Lz ≤ Lcz`.
  have hkey : ∀ ε : ℝ, 0 < ε → (((1 + ε : ℝ) : EReal)) * Lz ≤ Lcz := by
    intro ε hε
    -- eventually `c n ≤ 1 + ε`, hence `(1+ε) * z n ≤ c n * z n` (as `z n ≤ 0`).
    have hev : ∀ᶠ n in l, ((((1 + ε) * z n : ℝ)) : EReal) ≤ ((c n * z n : ℝ) : EReal) := by
      have : ∀ᶠ n in l, c n ≤ 1 + ε := by
        have hevent : ∀ᶠ n in l, dist (c n) 1 < ε :=
          (Metric.tendsto_nhds.1 hctend) ε hε
        filter_upwards [hevent] with n hn
        rw [Real.dist_eq, abs_lt] at hn
        linarith [hn.2]
      filter_upwards [this] with n hcn
      refine EReal.coe_le_coe_iff.2 ?_
      exact _root_.mul_le_mul_of_nonpos_right hcn (hz n)
    have hmono : Filter.liminf (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) l ≤ Lcz :=
      Filter.liminf_le_liminf hev
    -- `liminf ↑((1+ε)·z) = ↑(1+ε) * liminf ↑z = ↑(1+ε) * Lz`.
    have hscalar : Filter.liminf (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) l
        = (((1 + ε : ℝ) : EReal)) * Lz := by
      have hfun : (fun n => ((((1 + ε) * z n : ℝ)) : EReal))
          = fun n => (((1 + ε : ℝ) : EReal)) * ((z n : ℝ) : EReal) := by
        funext n; rw [EReal.coe_mul]
      rw [hfun, hLz, EReal.liminf_const_mul_of_nonneg_of_ne_top (by positivity)
        (EReal.coe_ne_top _)]
    rwa [hscalar] at hmono
  -- Pass `ε → 0⁺`.  `Lz ≤ 0`, so either `Lz = ⊥` or `Lz` is finite.
  rcases eq_bot_or_bot_lt Lz with hbot | hfin
  · rw [hbot]; exact bot_le
  · -- finite case: `Lz = ↑a` with `a := Lz.toReal`.
    have hne_bot : Lz ≠ ⊥ := hfin.ne'
    have hne_top : Lz ≠ ⊤ := (hLz0.trans_lt (by norm_num : (0 : EReal) < ⊤)).ne
    set a : ℝ := Lz.toReal with hadef
    have ha : ((a : ℝ) : EReal) = Lz := EReal.coe_toReal hne_top hne_bot
    rw [← ha]
    -- `↑((1+ε)·a) ≤ Lcz` for all `ε > 0`; `(1+ε)·a → a`; conclude `↑a ≤ Lcz`.
    have hreal : ∀ ε : ℝ, 0 < ε → ((((1 + ε) * a : ℝ)) : EReal) ≤ Lcz := by
      intro ε hε
      have := hkey ε hε
      rw [← ha, ← EReal.coe_mul] at this
      exact this
    -- `Tendsto (fun ε => ↑((1+ε)·a)) (𝓝[>] 0) (𝓝 ↑a)`, and `Lcz` closed-above bound.
    have htend : Tendsto (fun ε : ℝ => ((((1 + ε) * a : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 ((a : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have : Tendsto (fun ε : ℝ => (1 + ε) * a) (𝓝 0) (𝓝 ((1 + 0) * a)) :=
        ((continuous_const.add continuous_id).mul continuous_const).tendsto 0
      simp only [add_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hreal ε hε

/-- **Limsup under an asymptotically unit factor.** If `z ≤ 0` pointwise and `c → 1`, then
`limsup ↑z ≤ limsup ↑(c * z)`. -/
theorem limsup_coe_le_limsup_coe_mul_of_nonpos {ι : Type*} {l : Filter ι} [NeBot l]
    {c z : ι → ℝ} (hz : ∀ i, z i ≤ 0)
    (hctend : Tendsto c l (𝓝 1)) :
    Filter.limsup (fun n => ((z n : ℝ) : EReal)) l
      ≤ Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) l := by
  set Lz : EReal := Filter.limsup (fun n => ((z n : ℝ) : EReal)) l with hLz
  set Lcz : EReal := Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) l with hLcz
  have hLz0 : Lz ≤ 0 := by
    rw [hLz]
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall fun n =>
      (EReal.coe_le_coe_iff.2 (hz n) : ((z n : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)))) ?_
    simp [Filter.limsup_const]
  have hkey : ∀ ε : ℝ, 0 < ε → (((1 + ε : ℝ) : EReal)) * Lz ≤ Lcz := by
    intro ε hε
    have hev : ∀ᶠ n in l, ((((1 + ε) * z n : ℝ)) : EReal) ≤ ((c n * z n : ℝ) : EReal) := by
      have : ∀ᶠ n in l, c n ≤ 1 + ε := by
        have hevent : ∀ᶠ n in l, dist (c n) 1 < ε :=
          (Metric.tendsto_nhds.1 hctend) ε hε
        filter_upwards [hevent] with n hn
        rw [Real.dist_eq, abs_lt] at hn
        linarith [hn.2]
      filter_upwards [this] with n hcn
      exact EReal.coe_le_coe_iff.2 (_root_.mul_le_mul_of_nonpos_right hcn (hz n))
    have hmono : Filter.limsup (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) l ≤ Lcz :=
      Filter.limsup_le_limsup hev
    have hscalar : Filter.limsup (fun n => ((((1 + ε) * z n : ℝ)) : EReal)) l
        = (((1 + ε : ℝ) : EReal)) * Lz := by
      have hfun : (fun n => ((((1 + ε) * z n : ℝ)) : EReal))
          = fun n => (((1 + ε : ℝ) : EReal)) * ((z n : ℝ) : EReal) := by
        funext n; rw [EReal.coe_mul]
      rw [hfun, hLz, EReal.limsup_const_mul_of_nonneg_of_ne_top (by positivity)
        (EReal.coe_ne_top _)]
    rwa [hscalar] at hmono
  rcases eq_bot_or_bot_lt Lz with hbot | hfin
  · rw [hbot]; exact bot_le
  · have hne_bot : Lz ≠ ⊥ := hfin.ne'
    have hne_top : Lz ≠ ⊤ := (hLz0.trans_lt (by norm_num : (0 : EReal) < ⊤)).ne
    set a : ℝ := Lz.toReal with hadef
    have ha : ((a : ℝ) : EReal) = Lz := EReal.coe_toReal hne_top hne_bot
    rw [← ha]
    have hreal : ∀ ε : ℝ, 0 < ε → ((((1 + ε) * a : ℝ)) : EReal) ≤ Lcz := by
      intro ε hε
      have := hkey ε hε
      rw [← ha, ← EReal.coe_mul] at this
      exact this
    have htend : Tendsto (fun ε : ℝ => ((((1 + ε) * a : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 ((a : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have : Tendsto (fun ε : ℝ => (1 + ε) * a) (𝓝 0) (𝓝 ((1 + 0) * a)) :=
        ((continuous_const.add continuous_id).mul continuous_const).tendsto 0
      simp only [add_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hreal ε hε

/-- **Limsup under an asymptotically unit factor.** If `z ≤ 0` pointwise and `c → 1`, then
`limsup ↑(c * z) ≤ limsup ↑z`. -/
theorem limsup_coe_mul_le_limsup_coe_of_nonpos {ι : Type*} {l : Filter ι} [NeBot l]
    {c z : ι → ℝ} (hz : ∀ i, z i ≤ 0)
    (hctend : Tendsto c l (𝓝 1)) :
    Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) l
      ≤ Filter.limsup (fun n => ((z n : ℝ) : EReal)) l := by
  set Lz : EReal := Filter.limsup (fun n => ((z n : ℝ) : EReal)) l with hLz
  set Lcz : EReal := Filter.limsup (fun n => ((c n * z n : ℝ) : EReal)) l with hLcz
  have hLz0 : Lz ≤ 0 := by
    rw [hLz]
    refine le_trans (Filter.limsup_le_limsup (Eventually.of_forall fun n =>
      (EReal.coe_le_coe_iff.2 (hz n) : ((z n : ℝ) : EReal) ≤ ((0 : ℝ) : EReal)))) ?_
    simp [Filter.limsup_const]
  -- For every `ε ∈ (0,1)`: `Lcz ≤ ↑(1−ε) * Lz`.
  have hkey : ∀ ε : ℝ, 0 < ε → ε < 1 → Lcz ≤ (((1 - ε : ℝ) : EReal)) * Lz := by
    intro ε hε hε1
    have hev : ∀ᶠ n in l, ((c n * z n : ℝ) : EReal) ≤ ((((1 - ε) * z n : ℝ)) : EReal) := by
      have : ∀ᶠ n in l, 1 - ε ≤ c n := by
        have hevent : ∀ᶠ n in l, dist (c n) 1 < ε :=
          (Metric.tendsto_nhds.1 hctend) ε hε
        filter_upwards [hevent] with n hn
        rw [Real.dist_eq, abs_lt] at hn
        linarith [hn.1]
      filter_upwards [this] with n hcn
      exact EReal.coe_le_coe_iff.2 (_root_.mul_le_mul_of_nonpos_right hcn (hz n))
    have hmono : Lcz ≤ Filter.limsup (fun n => ((((1 - ε) * z n : ℝ)) : EReal)) l :=
      Filter.limsup_le_limsup hev
    have hscalar : Filter.limsup (fun n => ((((1 - ε) * z n : ℝ)) : EReal)) l
        = (((1 - ε : ℝ) : EReal)) * Lz := by
      have hfun : (fun n => ((((1 - ε) * z n : ℝ)) : EReal))
          = fun n => (((1 - ε : ℝ) : EReal)) * ((z n : ℝ) : EReal) := by
        funext n; rw [EReal.coe_mul]
      rw [hfun, hLz, EReal.limsup_const_mul_of_nonneg_of_ne_top
        (EReal.coe_nonneg.2 (by linarith)) (EReal.coe_ne_top _)]
    rwa [hscalar] at hmono
  rcases eq_bot_or_bot_lt Lz with hbot | hfin
  · -- `Lz = ⊥`: then `↑(1−ε)·⊥ = ⊥` for `1−ε > 0`, so `Lcz ≤ ⊥ = Lz`.
    rw [hbot]
    have := hkey (1/2) (by norm_num) (by norm_num)
    rw [hbot] at this
    rwa [EReal.mul_bot_of_pos
      (EReal.coe_pos.2 (by norm_num : (0 : ℝ) < 1 - 1/2))] at this
  · have hne_bot : Lz ≠ ⊥ := hfin.ne'
    have hne_top : Lz ≠ ⊤ := (hLz0.trans_lt (by norm_num : (0 : EReal) < ⊤)).ne
    set a : ℝ := Lz.toReal with hadef
    have ha : ((a : ℝ) : EReal) = Lz := EReal.coe_toReal hne_top hne_bot
    rw [← ha]
    have hreal : ∀ ε : ℝ, 0 < ε → ε < 1 → Lcz ≤ ((((1 - ε) * a : ℝ)) : EReal) := by
      intro ε hε hε1
      have := hkey ε hε hε1
      rw [← ha, ← EReal.coe_mul] at this
      exact this
    have htend : Tendsto (fun ε : ℝ => ((((1 - ε) * a : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 ((a : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      have : Tendsto (fun ε : ℝ => (1 - ε) * a) (𝓝 0) (𝓝 ((1 - 0) * a)) :=
        ((continuous_const.sub continuous_id).mul continuous_const).tendsto 0
      simp only [sub_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε hε1
    exact hreal ε hε hε1

end EReal
