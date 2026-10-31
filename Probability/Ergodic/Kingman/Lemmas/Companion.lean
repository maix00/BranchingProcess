/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
module

import Probability.Ergodic.Kingman.Basic
import Order.EReal.LiminfLimsup
import MeasureTheory.Integral.MeasurePreserving

/-!
# Reduction to the non-positive companion cocycle

Karlsson's §3.3 reduction running the argument on the *non-positive* companion cocycle: the
`T^[M]`-subsequence cocycle algebra and the `EReal`-envelope `T`-invariance in the non-positive
case.

Non-reusable proof support for `ProbabilityTheory.Ergodic.Kingman.Theorem`: the non-positive
companion cocycle, its block subsequences, and the associated `EReal` envelope comparisons.

## Internal proof declarations

These declarations are imported only by the neighboring Kingman proof modules:

* `vcoc g n x = g n x - birkhoffSum T (g 1) n x` is the non-positive companion cocycle.
  `vcoc_subadditive`, `vcoc_nonpos`, and `vcoc_integrable` state, respectively, its
  subadditivity, `vcoc g (n+1) x ≤ 0`, and levelwise integrability.
  `vcoc_bddBelow` transfers a lower bound on `((∫ g (n+1))/(n+1))ₙ` to
  `((∫ vcoc g (n+1))/(n+1))ₙ`; `ecdiv_eq_ecdiv_vcoc_add` gives
  `ecdiv g n x = ecdiv (vcoc g) n x + ↑(birkhoffAverage ℝ T (g 1) (n+1) x)`.
* `vM g M n x = g (n*M) x - ∑_{i<n} g M (T^[i*M] x)` is the block-subsequence
  companion over `T^[M]`. `vM_subadditive`, `vM_nonpos`, `vM_integrable`,
  `vM_measurePreserving`, and `integral_vM` give its cocycle, sign, integrability,
  measure-preserving transformation, and integral properties.
* `block_sandwich` states `g ((k+1)*M) x ≤ g m x ≤ g (k*M) x` when
  `k*M ≤ m ≤ (k+1)*M` for a non-positive subadditive cocycle.
* `cdiv_le_shift` states
  `cdiv g n x ≤ g 1 x/(n+1) + g n (T x)/(n+1)`;
  `aemeasurable_ereal_liminf` and `aemeasurable_ereal_limsup` give a.e. measurability
  of the corresponding envelopes.
* `liminf_ecdiv_comp_ae` and `limsup_ecdiv_comp_ae` prove the a.e. invariance
  \[
    (x\mapsto\liminf_n\operatorname{ecdiv}(g,n,x))\circ T
      =^{\mu}_{\mathrm{ae}}(x\mapsto\liminf_n\operatorname{ecdiv}(g,n,x)),
  \]
  and the corresponding identity with `limsup`, under the non-positive
  companion-cocycle hypotheses.

## References

* The proof of the unnumbered theorem labeled “Theorem (Kingman, 1968)” in Section 3.3 of
  Anders Karlsson, “A Proof of the Subadditive Ergodic Theorem,” Chapter 12 in *Groups, Graphs
  and Random Walks*, London Mathematical Society Lecture Note Series 436, Cambridge University
  Press (2017), pp. 343–354, DOI 10.1017/9781316576571.014. The companion cocycle corresponds to
  Karlsson's `v_n` in the proof of that theorem.

-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-! ### Reduction to the non-positive companion cocycle

Karlsson's §3.3 argument is run on the *non-positive* companion
`vcoc g n := g n − birkhoffSum T (g 1) n`. Since `birkhoffSum (g 1)` is an additive cocycle,
`vcoc g` is again subadditive, and `le_birkhoffSum_one` gives `vcoc g (n+1) ≤ 0`.
The normalized gap is unchanged: `cdiv g − cdiv (vcoc g) = birkhoffAverage (g 1) (·+1)`, which
converges a.e. (Birkhoff) to the *finite* `μ[g 1 | invariants T]`, so `liminf = limsup` for
`ecdiv g`
follows from the same statement for `ecdiv (vcoc g)`. -/

/-- The **non-positive companion cocycle** `vcoc g n x := g n x − birkhoffSum T (g 1) n x`. -/
noncomputable def vcoc (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ :=
  g n x - birkhoffSum T (g 1) n x

omit [MeasurableSpace X] in
/-- `vcoc g` is a subadditive cocycle: subtracting the *additive* cocycle `birkhoffSum (g 1)`
from the subadditive `g` preserves subadditivity. -/
lemma vcoc_subadditive {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) :
    IsSubadditiveCocycle T (vcoc (T := T) g) := by
  refine ⟨fun m n x => ?_⟩
  simp only [vcoc]
  have hadd : birkhoffSum T (g 1) (m + n) x
      = birkhoffSum T (g 1) m x + birkhoffSum T (g 1) n (T^[m] x) :=
    birkhoffSum_add_right_apply T (g 1) m n x
  have hg := hsub.apply_add_le m n x
  rw [hadd]
  linarith

omit [MeasurableSpace X] in
/-- `vcoc g (n+1) x ≤ 0`: exactly `le_birkhoffSum_one`. -/
lemma vcoc_nonpos {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    vcoc (T := T) g (n + 1) x ≤ 0 := by
  simp only [vcoc, sub_nonpos]
  exact hsub.le_birkhoffSum_one n x

/-- Each level of `vcoc g` is integrable (a difference of integrable `g n` and `birkhoffSum`). -/
lemma vcoc_integrable (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (vcoc (T := T) g n) μ := by
  have heq : vcoc (T := T) g n = fun x => g n x - birkhoffSum T (g 1) n x := rfl
  rw [heq]
  exact (hint n).sub (integrable_birkhoffSum hT (hint 1) n)

/-- The integral of `vcoc g (n+1)` is `(∫ g (n+1)) − (n+1)·(∫ g 1)`: the additive cocycle
`birkhoffSum (g 1)` integrates to `(n+1)·∫ g 1` by measure preservation. -/
private lemma integral_vcoc (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    ∫ x, vcoc (T := T) g (n + 1) x ∂μ
      = (∫ x, g (n + 1) x ∂μ) - ((n : ℝ) + 1) * ∫ x, g 1 x ∂μ := by
  simp only [vcoc]
  rw [integral_sub (hint (n + 1)) (integrable_birkhoffSum hT (hint 1) (n + 1))]
  congr 1
  -- `∫ birkhoffSum T (g 1) (n+1) = (n+1) * ∫ g 1`.
  simp only [birkhoffSum]
  rw [integral_finsetSum (f := fun k x => g 1 (T^[k] x)) _
    (fun j _ => (hT.iterate j).integrable_comp_of_integrable (hint 1))]
  have : ∀ j ∈ Finset.range (n + 1), ∫ x, g 1 (T^[j] x) ∂μ = ∫ x, g 1 x ∂μ :=
    fun j _ => (hT.iterate j).integral_comp_of_integrable (hint 1)
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- The normalized integrals of `vcoc g` are bounded below: `(∫ vcoc(n+1))/(n+1)
= (∫ g(n+1))/(n+1) − ∫ g 1`, a shift of the bounded-below sequence `hbdd`. -/
lemma vcoc_bddBelow (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    BddBelow (Set.range fun n : ℕ => (∫ x, vcoc (T := T) g (n + 1) x ∂μ) / (n + 1)) := by
  obtain ⟨c, hc⟩ := hbdd
  refine ⟨c - ∫ x, g 1 x ∂μ, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp only
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcn : c ≤ (∫ x, g (n + 1) x ∂μ) / (n + 1) := hc ⟨n, rfl⟩
  have hval : (∫ x, vcoc (T := T) g (n + 1) x ∂μ) / ((n : ℝ) + 1)
      = (∫ x, g (n + 1) x ∂μ) / ((n : ℝ) + 1) - ∫ x, g 1 x ∂μ := by
    rw [integral_vcoc hT hint n, sub_div]
    congr 1
    rw [mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]
  rw [hval]
  linarith

omit [MeasurableSpace X] in
/-- **Gap-transfer identity.** Pointwise in `EReal`, the normalized `g`-cocycle is the
normalized companion plus the Birkhoff average of `g 1`:
`ecdiv g n x = ecdiv (vcoc g) n x + ↑(birkhoffAverage ℝ T (g 1) (n+1) x)`. -/
lemma ecdiv_eq_ecdiv_vcoc_add {g : ℕ → X → ℝ} (n : ℕ) (x : X) :
    ecdiv g n x
      = ecdiv (vcoc (T := T) g) n x + ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal) := by
  simp only [ecdiv, ← EReal.coe_add]
  congr 1
  simp only [cdiv, vcoc, birkhoffAverage, smul_eq_mul, sub_div]
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, div_eq_inv_mul]
  ring

/-! ### The `Tᴹ`-subsequence cocycle algebra

For a non-positive subadditive cocycle `g` over `T` and a block length `M`, the
`Tᴹ`-subsequence cocycle `vM g M n x := g (n*M) x − ∑_{i<n} g M (T^[i*M] x)` is a non-positive
subadditive cocycle for `T^[M]`. This is a pure-algebra layer; no measure theory is used. -/

/-- The **`Tᴹ`-subsequence cocycle** `vM g M n x := g (n*M) x − ∑_{i<n} g M (T^[i*M] x)`. -/
noncomputable def vM (g : ℕ → X → ℝ) (M n : ℕ) (x : X) : ℝ :=
  g (n * M) x - ∑ i ∈ Finset.range n, g M (T^[i * M] x)

omit [MeasurableSpace X] in
/-- `vM g M` is a subadditive cocycle for `T^[M]`. Block subadditivity of `g` over the split
`(n+p)·M = n·M + p·M` gives the `g`-term bound; the sum splits as `range (n+p) = range n ∪ tail`,
and reindexing the tail `i = n+j` lines up `T^[i*M] = (T^[M])^[n] (T^[j*M])`. -/
lemma vM_subadditive {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (M : ℕ) :
    IsSubadditiveCocycle (T^[M]) (vM (T := T) g M) := by
  refine ⟨fun n p x => ?_⟩
  simp only [vM]
  -- frontier identity `T^[n*M] x = (T^[M])^[n] x`.
  have hfront : T^[n * M] x = (T^[M])^[n] x := by
    rw [← Function.iterate_mul]; congr 1; ring
  -- `g`-term: `g ((n+p)*M) x ≤ g (n*M) x + g (p*M) ((T^[M])^[n] x)`.
  have hgsplit : g ((n + p) * M) x ≤ g (n * M) x + g (p * M) ((T^[M])^[n] x) := by
    have := hsub.apply_add_le (n * M) (p * M) x
    rw [← Nat.add_mul, hfront] at this
    exact this
  -- sum split: `range (n+p) = range n ∪ (shifted range p)`, tail reindexed to the orbit frontier.
  have hsum : ∑ i ∈ Finset.range (n + p), g M (T^[i * M] x)
      = (∑ i ∈ Finset.range n, g M (T^[i * M] x))
        + ∑ i ∈ Finset.range p, g M (T^[i * M] ((T^[M])^[n] x)) := by
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [← hfront, ← Function.iterate_add_apply]
    congr 1
    ring
  rw [hsum]
  -- linear arithmetic on the three sums.
  set Sn := ∑ i ∈ Finset.range n, g M (T^[i * M] x)
  set Sp := ∑ i ∈ Finset.range p, g M (T^[i * M] ((T^[M])^[n] x))
  linarith

omit [MeasurableSpace X] in
/-- `vM g M n ≤ 0` for `n ≥ 1` when `g` is non-positive subadditive: block subadditivity
(`le_sum_blocks` with all `n` blocks equal to `M`) gives `g (n*M) ≤ ∑_{i<n} g M (T^[i*M])`. -/
lemma vM_nonpos {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (M n : ℕ)
    (hn : 1 ≤ n) (x : X) : vM (T := T) g M n x ≤ 0 := by
  simp only [vM, sub_nonpos]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- `le_sum_blocks` with constant block-length `ℓ = fun _ => M` and `k+1` blocks.
  have hblk := hsub.le_sum_blocks (fun _ => M) k x
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hblk
  exact hblk

/-- Each level `vM g M n` is integrable for measure-preserving `T` (a finite difference of
integrable terms; each `g M (T^[i*M] ·)` is integrable since `T^[i*M]` is measure-preserving). -/
lemma vM_integrable (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (M n : ℕ) :
    Integrable (vM (T := T) g M n) μ := by
  have heq : vM (T := T) g M n
      = fun x => g (n * M) x - ∑ i ∈ Finset.range n, g M (T^[i * M] x) := rfl
  rw [heq]
  refine (hint (n * M)).sub ?_
  exact integrable_finsetSum _
    (fun i _ => (hT.iterate (i * M)).integrable_comp_of_integrable (hint M))

/-- `T^[M]` is measure-preserving for measure-preserving `T` (stated for downstream use). -/
lemma vM_measurePreserving (hT : MeasurePreserving T μ μ) (M : ℕ) :
    MeasurePreserving (T^[M]) μ μ := hT.iterate M

/-- The integral of `vM g M n` is `(∫ g (n*M)) − n·(∫ g M)`: the orbit-sum integrates to
`n·∫ g M` by measure preservation. -/
lemma integral_vM (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (M n : ℕ) :
    ∫ x, vM (T := T) g M n x ∂μ = (∫ x, g (n * M) x ∂μ) - (n : ℝ) * ∫ x, g M x ∂μ := by
  have hintsum : Integrable (fun x => ∑ i ∈ Finset.range n, g M (T^[i * M] x)) μ :=
    integrable_finsetSum _ (fun i _ => (hT.iterate (i * M)).integrable_comp_of_integrable (hint M))
  have hsplit : ∫ x, vM (T := T) g M n x ∂μ
      = (∫ x, g (n * M) x ∂μ) - ∫ x, ∑ i ∈ Finset.range n, g M (T^[i * M] x) ∂μ := by
    rw [show (fun x => vM (T := T) g M n x)
      = fun x => g (n * M) x - ∑ i ∈ Finset.range n, g M (T^[i * M] x) from rfl]
    exact integral_sub (hint (n * M)) hintsum
  rw [hsplit]
  congr 1
  rw [integral_finsetSum (f := fun i x => g M (T^[i * M] x)) _
    (fun i _ => (hT.iterate (i * M)).integrable_comp_of_integrable (hint M))]
  have : ∀ i ∈ Finset.range n, ∫ x, g M (T^[i * M] x) ∂μ = ∫ x, g M x ∂μ :=
    fun i _ => (hT.iterate (i * M)).integral_comp_of_integrable (hint M)
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [MeasurableSpace X] in
/-- **Block sandwich (non-positive case).** For a non-positive subadditive cocycle and a block
length `M`, when `k*M ≤ m ≤ (k+1)*M` the cocycle value `g m x` is sandwiched:
`g ((k+1)*M) x ≤ g m x ≤ g (k*M) x`. (Upper bound: `g m = g (kM + (m−kM)) ≤ g (kM) + g (m−kM)(…) ≤
g (kM)` since `g (m−kM) ≤ 0`; the offset `0` case is equality. Lower bound symmetric using
`(k+1)M = m + ((k+1)M − m)`.) -/
lemma block_sandwich {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) (M k m : ℕ) (hkm : k * M ≤ m) (hmk : m ≤ (k + 1) * M)
    (x : X) : g ((k + 1) * M) x ≤ g m x ∧ g m x ≤ g (k * M) x := by
  have hnp : ∀ j, 1 ≤ j → ∀ y, g j y ≤ 0 := by
    intro j hj y; obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩; exact hnonpos i y
  constructor
  · -- `g ((k+1)*M) x ≤ g m x`: split `(k+1)*M = m + s`, `s = (k+1)*M − m`.
    set s : ℕ := (k + 1) * M - m with hs
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · have : (k + 1) * M = m := by omega
      rw [this]
    · have hsplit : (k + 1) * M = m + s := by omega
      calc g ((k + 1) * M) x = g (m + s) x := by rw [hsplit]
        _ ≤ g m x + g s (T^[m] x) := hsub.apply_add_le m s x
        _ ≤ g m x := by linarith [hnp s hspos (T^[m] x)]
  · -- `g m x ≤ g (k*M) x`: split `m = k*M + r`, `r = m − k*M`.
    set r : ℕ := m - k * M with hr
    rcases Nat.eq_zero_or_pos r with hr0 | hrpos
    · have : m = k * M := by omega
      rw [this]
    · have hsplit : m = k * M + r := by omega
      calc g m x = g (k * M + r) x := by rw [hsplit]
        _ ≤ g (k * M) x + g r (T^[k * M] x) := hsub.apply_add_le (k * M) r x
        _ ≤ g (k * M) x := by linarith [hnp r hrpos (T^[k * M] x)]

omit [MeasurableSpace X] in
/-- The pointwise subadditivity bound, normalized:
`cdiv g n x ≤ g 1 x / (n+1) + g n (T x)/(n+1)`. -/
lemma cdiv_le_shift {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    cdiv g n x ≤ g 1 x / (n + 1) + g n (T x) / (n + 1) := by
  have h := hsub.apply_add_le 1 n x
  rw [show (1 + n) = n + 1 from by ring] at h
  rw [cdiv, ← add_div]
  apply div_le_div_of_nonneg_right h (by positivity) |>.trans_eq
  simp only [Function.iterate_one]

/-! ### `EReal`-envelope `T`-invariance (non-positive case)

The generic `EReal` translation and vanishing-perturbation rules used below
are stated for arbitrary filters in `Order.EReal.LiminfLimsup`. This module
uses them for the normalized cocycle envelopes. -/

/-- The `EReal` `liminf` envelope `x ↦ liminf (ecdiv g · x)` is a.e. measurable: it agrees a.e.
with the `EReal` liminf of measurable representatives of each level. -/
lemma aemeasurable_ereal_liminf {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.liminf (fun n => ecdiv g n x) atTop) μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.liminf (fun n => ((g₀ (n + 1) x / (n + 1) : ℝ) : EReal)) atTop, ?_, ?_⟩
  · exact Measurable.liminf (fun n => ((hg₀m (n + 1)).div_const _).coe_real_ereal)
  · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [ecdiv, cdiv]
    congr 1
    funext n
    rw [hx n]

/-- The `EReal` `limsup` envelope `x ↦ limsup (ecdiv g · x)` is a.e. measurable. -/
lemma aemeasurable_ereal_limsup {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.limsup (fun n => ecdiv g n x) atTop) μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.limsup (fun n => ((g₀ (n + 1) x / (n + 1) : ℝ) : EReal)) atTop, ?_, ?_⟩
  · exact Measurable.limsup (fun n => ((hg₀m (n + 1)).div_const _).coe_real_ereal)
  · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [ecdiv, cdiv]
    congr 1
    funext n
    rw [hx n]

omit [MeasurableSpace X] in
/-- The shift-and-ratio lower bound on the cocycle at `T x` (non-positive case): for every `k`,
`cdiv g k (T x) ≥ c k · z k − g 1 x/(k+1)`, where `z k := cdiv g (k+1) x ≤ 0` and
`c k := (k+2)/(k+1) ≥ 1`. From `g (k+2) x ≤ g 1 x + g (k+1) (T x)` (subadditivity, first block of
length `1`), so `g (k+1) (T x) ≥ g (k+2) x − g 1 x`; dividing by `k+1` and rewriting
`g (k+2) x/(k+1) = (k+2)/(k+1) · cdiv g (k+1) x`. -/
private lemma cdiv_comp_ge_ratio {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (k : ℕ)
    (x : X) :
    ((k : ℝ) + 2) / ((k : ℝ) + 1) * cdiv g (k + 1) x - g 1 x / ((k : ℝ) + 1)
      ≤ cdiv g k (T x) := by
  have h := hsub.apply_add_le 1 (k + 1) x
  rw [show (1 + (k + 1)) = k + 2 from by ring, Function.iterate_one] at h
  -- `g (k+2) x ≤ g 1 x + g (k+1) (T x)`, so `g (k+1) (T x) ≥ g (k+2) x − g 1 x`.
  have hge : g (k + 2) x - g 1 x ≤ g (k + 1) (T x) := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  -- Divide by `k+1`.
  have hdiv : (g (k + 2) x - g 1 x) / ((k : ℝ) + 1) ≤ g (k + 1) (T x) / ((k : ℝ) + 1) :=
    div_le_div_of_nonneg_right hge hk1.le
  -- Rewrite both sides to the target form.
  have hlhs : ((k : ℝ) + 2) / ((k : ℝ) + 1) * cdiv g (k + 1) x - g 1 x / ((k : ℝ) + 1)
      = (g (k + 2) x - g 1 x) / ((k : ℝ) + 1) := by
    simp only [cdiv]
    rw [show (((k : ℕ) + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring]
    field_simp
  rw [hlhs]
  change (g (k + 2) x - g 1 x) / ((k : ℝ) + 1) ≤ g (k + 1) (T x) / ((k : ℝ) + 1)
  exact hdiv

omit [MeasurableSpace X] in
/-- The ratio sequence `c k := (k+2)/(k+1)` is `≥ 1` and tends to `1`. -/
private lemma ratio_succ_tendsto_one :
    Tendsto (fun k : ℕ => ((k : ℝ) + 2) / ((k : ℝ) + 1)) atTop (𝓝 1) := by
  have hform : (fun k : ℕ => ((k : ℝ) + 2) / ((k : ℝ) + 1))
      = fun k : ℕ => 1 + ((k : ℝ) + 1)⁻¹ := by
    funext k
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hform]
  have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp this
  simpa using tendsto_const_nhds.add hinv

omit [MeasurableSpace X] in
/-- **EReal `liminf` comparison (non-positive case).** For every `x`,
`liminf (ecdiv g · x) ≤ liminf (ecdiv g · (T x))`. From the shift-and-ratio lower bound
`cdiv_comp_ge_ratio`, the ratio squeeze `EReal.liminf_coe_le_liminf_coe_mul_of_nonpos` (using `cdiv g (k+1) x ≤ 0`), the
vanishing perturbation `g 1 x/(k+1) → 0`, and the index shift `liminf (cdiv g · x) =
liminf (cdiv g (·+1) x)`. -/
private lemma ereal_liminf_le_comp {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) (x : X) :
    Filter.liminf (fun n => ecdiv g n x) atTop
      ≤ Filter.liminf (fun n => ecdiv g n (T x)) atTop := by
  -- `z k := cdiv g (k+1) x ≤ 0`, `c k := (k+2)/(k+1)`, lower bound `y k := c k · z k − g1x/(k+1)`.
  set z : ℕ → ℝ := fun k => cdiv g (k + 1) x with hzdef
  set c : ℕ → ℝ := fun k => ((k : ℝ) + 2) / ((k : ℝ) + 1) with hcdef
  have hz : ∀ k, z k ≤ 0 := fun k => by
    simp only [hzdef, cdiv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [show (k + 1 + 1) = (k + 1) + 1 from rfl]; exact hnonpos (k + 1) x
  -- bound `cdiv g k (T x) ≥ c k · z k − g1x/(k+1)`.
  have hbound : ∀ k, c k * z k - g 1 x / ((k : ℝ) + 1) ≤ cdiv g k (T x) :=
    fun k => cdiv_comp_ge_ratio hsub k x
  -- chain of EReal inequalities.
  calc Filter.liminf (fun n => ecdiv g n x) atTop
      = Filter.liminf (fun k => ((z k : ℝ) : EReal)) atTop := by
        rw [hzdef]
        exact (Filter.liminf_nat_add (fun n => ((cdiv g n x : ℝ) : EReal)) 1).symm
    _ ≤ Filter.liminf (fun k => ((c k * z k : ℝ) : EReal)) atTop := by
        have hct : Tendsto c atTop (𝓝 1) := by rw [hcdef]; exact ratio_succ_tendsto_one
        exact EReal.liminf_coe_le_liminf_coe_mul_of_nonpos hz hct
    _ = Filter.liminf (fun k => ((c k * z k - g 1 x / ((k : ℝ) + 1) : ℝ) : EReal)) atTop := by
        refine EReal.liminf_coe_eq_of_sub_tendsto_zero ?_
        have : (fun k => c k * z k - (c k * z k - g 1 x / ((k : ℝ) + 1)))
            = fun k : ℕ => g 1 x / ((k : ℝ) + 1) := by funext k; ring
        rw [this]
        simp only [div_eq_mul_inv]
        have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          have : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
            tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
          exact tendsto_inv_atTop_zero.comp this
        simpa using hinv.const_mul (g 1 x)
    _ ≤ Filter.liminf (fun k => ((cdiv g k (T x) : ℝ) : EReal)) atTop := by
        refine Filter.liminf_le_liminf (Eventually.of_forall fun k =>
          EReal.coe_le_coe_iff.2 (hbound k)) ?_ ?_
        · exact Filter.isBounded_ge_of_bot
        · exact Filter.isCobounded_ge_of_top
    _ = Filter.liminf (fun n => ecdiv g n (T x)) atTop := rfl

omit [MeasurableSpace X] in
/-- **EReal `limsup` comparison (non-positive case).** For every `x`,
`limsup (ecdiv g · x) ≤ limsup (ecdiv g · (T x))`. Same route as `ereal_liminf_le_comp` with
`EReal.limsup_coe_le_limsup_coe_mul_of_nonpos` and `EReal.limsup_coe_eq_of_sub_tendsto_zero`. -/
private lemma ereal_limsup_le_comp {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) (x : X) :
    Filter.limsup (fun n => ecdiv g n x) atTop
      ≤ Filter.limsup (fun n => ecdiv g n (T x)) atTop := by
  set z : ℕ → ℝ := fun k => cdiv g (k + 1) x with hzdef
  set c : ℕ → ℝ := fun k => ((k : ℝ) + 2) / ((k : ℝ) + 1) with hcdef
  have hz : ∀ k, z k ≤ 0 := fun k => by
    simp only [hzdef, cdiv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [show (k + 1 + 1) = (k + 1) + 1 from rfl]; exact hnonpos (k + 1) x
  have hbound : ∀ k, c k * z k - g 1 x / ((k : ℝ) + 1) ≤ cdiv g k (T x) :=
    fun k => cdiv_comp_ge_ratio hsub k x
  calc Filter.limsup (fun n => ecdiv g n x) atTop
      = Filter.limsup (fun k => ((z k : ℝ) : EReal)) atTop := by
        rw [hzdef]
        exact (Filter.limsup_nat_add (fun n => ((cdiv g n x : ℝ) : EReal)) 1).symm
    _ ≤ Filter.limsup (fun k => ((c k * z k : ℝ) : EReal)) atTop := by
        have hct : Tendsto c atTop (𝓝 1) := by rw [hcdef]; exact ratio_succ_tendsto_one
        exact EReal.limsup_coe_le_limsup_coe_mul_of_nonpos hz hct
    _ = Filter.limsup (fun k => ((c k * z k - g 1 x / ((k : ℝ) + 1) : ℝ) : EReal)) atTop := by
        refine EReal.limsup_coe_eq_of_sub_tendsto_zero ?_
        have : (fun k => c k * z k - (c k * z k - g 1 x / ((k : ℝ) + 1)))
            = fun k : ℕ => g 1 x / ((k : ℝ) + 1) := by funext k; ring
        rw [this]
        simp only [div_eq_mul_inv]
        have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
          have : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
            tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
          exact tendsto_inv_atTop_zero.comp this
        simpa using hinv.const_mul (g 1 x)
    _ ≤ Filter.limsup (fun k => ((cdiv g k (T x) : ℝ) : EReal)) atTop := by
        refine Filter.limsup_le_limsup (Eventually.of_forall fun k =>
          EReal.coe_le_coe_iff.2 (hbound k)) ?_ ?_
        · exact Filter.isCobounded_le_of_bot
        · exact Filter.isBounded_le_of_top
    _ = Filter.limsup (fun n => ecdiv g n (T x)) atTop := rfl

/-- **EReal version of `ae_eq_comp_of_le_comp`.** For an a.e.-measurable `EReal`-valued `F`
with `F x ≤ F (T x)` a.e., `F ∘ T =ᵐ[μ] F`. Verbatim adaptation of the `ℝ` proof, with rational
levels `↑(c : ℚ) : EReal` and `EReal.exists_rat_btwn_of_lt` for the separation step. -/
private lemma ereal_ae_eq_comp_of_le_comp [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {F : X → EReal} (hF : AEMeasurable F μ)
    (hle : ∀ᵐ x ∂μ, F x ≤ F (T x)) : F ∘ T =ᵐ[μ] F := by
  set F0 : X → EReal := hF.mk F with hF0def
  have hF0m : Measurable F0 := hF.measurable_mk
  have hFF0 : F =ᵐ[μ] F0 := hF.ae_eq_mk
  have hkey : ∀ c : ℚ,
      T ⁻¹' {x | (((c : ℝ) : EReal)) ≤ F x} =ᵐ[μ] {x | (((c : ℝ) : EReal)) ≤ F x} := by
    intro c
    set s : Set X := {x | (((c : ℝ) : EReal)) ≤ F x} with hs
    have hsmeas : NullMeasurableSet s μ := by
      have hseq : s =ᵐ[μ] {x | (((c : ℝ) : EReal)) ≤ F0 x} := by
        rw [Filter.eventuallyEqSet_iff]
        filter_upwards [hFF0] with x hx
        simp only [hs, Set.mem_ofPred_eq, hx]
      exact (measurableSet_le measurable_const hF0m).nullMeasurableSet.congr hseq.symm
    have hsub : s ≤ᵐ[μ] T ⁻¹' s := by
      filter_upwards [hle] with x hx hxs
      have hxs' : (((c : ℝ) : EReal)) ≤ F x := hxs
      exact le_trans hxs' hx
    have hmeq : μ (T ⁻¹' s) = μ s := hT.measure_preimage hsmeas
    have : s =ᵐ[μ] T ⁻¹' s :=
      ae_eq_of_ae_subset_of_measure_ge hsub (le_of_eq hmeq) hsmeas (measure_ne_top μ _)
    exact this.symm
  have hall : ∀ᵐ x ∂μ, ∀ c : ℚ,
      (x ∈ T ⁻¹' {x | (((c : ℝ) : EReal)) ≤ F x}) ↔ (x ∈ {x | (((c : ℝ) : EReal)) ≤ F x}) := by
    rw [ae_all_iff]
    intro c
    exact Filter.eventuallyEqSet_iff.1 (hkey c)
  filter_upwards [hall] with x hx
  change F (T x) = F x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `F (T x) < F x`: pick rational `c` with `F (T x) < ↑c < F x`.
    obtain ⟨c, hc1, hc2⟩ := EReal.exists_rat_btwn_of_lt hlt
    have := (hx c).symm
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at this
    exact absurd (this.1 hc2.le) (not_le.2 hc1)
  · -- `F x < F (T x)`: pick rational `c` with `F x < ↑c < F (T x)`.
    obtain ⟨c, hc1, hc2⟩ := EReal.exists_rat_btwn_of_lt hgt
    have := hx c
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at this
    exact absurd (this.1 hc2.le) (not_le.2 hc1)

/-- **EReal `liminf`-envelope `T`-invariance (non-positive case).**
`(fun x => liminf (ecdiv g · x)) ∘ T =ᵐ[μ] …`. -/
lemma liminf_ecdiv_comp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) :
    (fun x => Filter.liminf (fun n => ecdiv g n x) atTop) ∘ T
      =ᵐ[μ] fun x => Filter.liminf (fun n => ecdiv g n x) atTop :=
  ereal_ae_eq_comp_of_le_comp hT (aemeasurable_ereal_liminf hint)
    (Eventually.of_forall (fun x => ereal_liminf_le_comp hsub hnonpos x))

/-- **EReal `limsup`-envelope `T`-invariance (non-positive case).**
`(fun x => limsup (ecdiv g · x)) ∘ T =ᵐ[μ] …`. -/
lemma limsup_ecdiv_comp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hnonpos : ∀ n x, g (n + 1) x ≤ 0) :
    (fun x => Filter.limsup (fun n => ecdiv g n x) atTop) ∘ T
      =ᵐ[μ] fun x => Filter.limsup (fun n => ecdiv g n x) atTop :=
  ereal_ae_eq_comp_of_le_comp hT (aemeasurable_ereal_limsup hint)
    (Eventually.of_forall (fun x => ereal_limsup_le_comp hsub hnonpos x))


end ProbabilityTheory.Kingman
