/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

import all Probability.Ergodic.Kingman.Basic
import Probability.Ergodic.Kingman.Fekete
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.AEMeasurable
import MeasureTheory.Integral.MeasurePreserving

/-!
# Fatou and envelope estimates for Kingman's theorem

This module contains the non-reusable proof chain controlling the EReal limsup and liminf of
`cdiv`, including a.e. measurability, the nonnegative Fatou defect, its liminf estimate, and
integrability of the limsup envelope. These declarations support the Kingman theorem proof and
are kept under `Lemmas/` because they depend on the specific cocycle normalization and its
Birkhoff-average defect.

## Internal proof declarations

* `aemeasurable_limsup_div` and `aemeasurable_liminf_div` show that
  `x ↦ limsupₙ g(n+1,x)/(n+1)` and `x ↦ liminfₙ g(n+1,x)/(n+1)` are a.e. measurable.
* `ae_bddAbove_cdiv` gives an a.e. upper bound on the range of the normalized cocycle.
* `ae_ereal_limsup_le_condExp` gives
  `limsupₙ ↑(g(n+1,x)/(n+1)) ≤ ↑(E[g(1) | invariants(T)](x))` a.e.
* `ae_bot_lt_ereal_limsup` gives `⊥ < limsupₙ ↑(g(n+1,x)/(n+1))` a.e. under a lower bound
  on the normalized integrals.
* `int_limsup_div_integrable_aux` proves integrability of
  `x ↦ limsupₙ g(n+1,x)/(n+1)` from the same hypotheses.

The principal envelope estimate is the almost-everywhere bound
\[
  \limsup_{n\to\infty}\frac{g(n+1,x)}{n+1}
       \le \mathbb E[g(1,\cdot)\mid\mathcal I_T](x),
\]
where $\mathcal I_T$ is the invariant sigma-algebra of $T$.

-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-! ### A.e. measurability of the limsup/liminf envelopes -/

/-- The pointwise `limsup` of `cdiv g · x` is a.e. measurable: it agrees a.e.
with the limsup of measurable representatives of each level `g (n+1)`. -/
lemma aemeasurable_limsup_div {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.limsup (fun n => cdiv g n x) atTop) μ := by
  -- Measurable representatives of each level.
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.limsup (fun n => g₀ (n + 1) x / (n + 1)) atTop, ?_, ?_⟩
  · exact Measurable.limsup (fun n => (hg₀m (n + 1)).div_const _)
  · -- The two sequences agree a.e. for all `n` simultaneously.
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [cdiv]
    congr 1
    funext n
    rw [hx n]

/-- The pointwise `liminf` of `cdiv g · x` is a.e. measurable. -/
lemma aemeasurable_liminf_div {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.liminf (fun n => cdiv g n x) atTop) μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  refine ⟨fun x => Filter.liminf (fun n => g₀ (n + 1) x / (n + 1)) atTop, ?_, ?_⟩
  · exact Measurable.liminf (fun n => (hg₀m (n + 1)).div_const _)
  · have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g (n + 1) x = g₀ (n + 1) x :=
      ae_all_iff.2 (fun n => hgg₀ (n + 1))
    filter_upwards [hall] with x hx
    simp only [cdiv]
    congr 1
    funext n
    rw [hx n]

/-! ### Boundedness of the normalized cocycle

A.e., the range of `cdiv g · x` is bounded above (immediate from `le_birkhoffSum_one` and
a.e. boundedness of
the Birkhoff averages of `g 1`). The bounded-below direction is the subtle one: subadditivity
gives only upper bounds, so a.e. finiteness of the liminf holds only once a.e. convergence is
known. Accordingly it is derived from the core lemma `ae_tendsto_cdiv` (a convergent sequence
is bounded), defined below. -/

/-- A.e. the range of `cdiv g · x` is bounded above (`le_birkhoffSum_one` +
`ae_bddAbove_birkhoffAverage`). -/
lemma ae_bddAbove_cdiv [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
    ∀ᵐ x ∂μ, BddAbove (Set.range fun n : ℕ => cdiv g n x) := by
  filter_upwards [ae_bddAbove_birkhoffAverage hT (hint 1)] with x hx
  obtain ⟨M, hM⟩ := hx
  refine ⟨M, ?_⟩
  rintro y ⟨n, rfl⟩
  exact le_trans (cdiv_le_birkhoffAverage hsub n x) (hM (Set.mem_range_self n))

/-! ### EReal envelope estimates -/

/-- **Envelope.** A.e. the `EReal` `limsup` of the normalized cocycle is bounded above by the
(finite) conditional expectation `μ[g 1 | invariants T]`, hence is `< ⊤`. From
`cdiv_le_birkhoffAverage` and the Birkhoff convergence `birkhoffAverage g₁ (n+1) → μ[g₁|I]`. -/
lemma ae_ereal_limsup_le_condExp [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
    ∀ᵐ x ∂μ, Filter.limsup (fun n => ecdiv g n x) atTop
      ≤ ((μ[g 1 | MeasurableSpace.invariants T] x : ℝ) : EReal) := by
  filter_upwards [tendsto_birkhoffAverage_ae hT (hint 1)] with x hBconv
  -- `A_{n+1}(g₁) x → B x`, so the shifted `EReal` sequence converges to `↑(B x)`.
  set B : ℝ := (μ[g 1 | MeasurableSpace.invariants T]) x with hBdef
  have hshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop (𝓝 B) :=
    hBconv.comp (tendsto_add_atTop_nat 1)
  have heshift : Tendsto (fun n : ℕ => ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal))
      atTop (𝓝 ((B : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hshift
  -- `limsup (ecdiv) ≤ limsup (↑A_{n+1}) = ↑B`.
  have hle : Filter.limsup (fun n => ecdiv g n x) atTop
      ≤ Filter.limsup (fun n : ℕ => ((birkhoffAverage ℝ T (g 1) (n + 1) x : ℝ) : EReal)) atTop := by
    refine Filter.limsup_le_limsup ?_ ?_ ?_
    · filter_upwards with n
      exact EReal.coe_le_coe_iff.2 (cdiv_le_birkhoffAverage hsub n x)
    · exact Filter.isCobounded_le_of_bot
    · exact Filter.isBounded_le_of_top
  rw [heshift.limsup_eq] at hle
  exact hle

/-! ### The Fatou step: finiteness of the limsup and integrability of `f₊`

The normalized cocycle satisfies `cdiv g n x ≤ birkhoffAverage ℝ T (g 1) (n+1) x`
(`le_birkhoffSum_one`), so the
nonnegative defect `d n x := birkhoffAverage ℝ T (g 1) (n+1) x − cdiv g n x ≥ 0` controls how
far `cdiv` can drop. A single `ℝ≥0∞` Fatou pass (`lintegral_liminf_le`) on `ENNReal.ofReal (d n)`
shows `liminf_n (d n x) < ∞` a.e., which (since the Birkhoff average converges) is exactly
`limsup_n (cdiv g n x) > −∞` a.e. (i.e. `⊥ < EReal limsup`), and also yields that the limsup
envelope `f₊` is integrable. -/

/-- The nonnegative Fatou defect `birkhoffAverage ℝ T (g 1) (n+1) x − cdiv g n x ≥ 0`. -/
private noncomputable def fdefect (g : ℕ → X → ℝ) (n : ℕ) (x : X) : ℝ :=
  birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x

omit [MeasurableSpace X] in
/-- The Fatou defect is nonnegative, by `cdiv_le_birkhoffAverage`. -/
private lemma fdefect_nonneg {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) (n : ℕ) (x : X) :
    0 ≤ fdefect (T := T) g n x :=
  sub_nonneg.2 (cdiv_le_birkhoffAverage hsub n x)

/-- `cdiv g n` is integrable (`g (n+1)` divided by a constant). -/
private lemma integrable_cdiv {g : ℕ → X → ℝ} (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (cdiv g n) μ := by
  have : cdiv g n = fun x => g (n + 1) x / ((n : ℝ) + 1) := rfl
  rw [this]
  exact (hint (n + 1)).div_const _

/-- `birkhoffAverage ℝ T (g 1) (n+1)` is integrable. -/
private lemma integrable_birkhoffAverage_one (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (fun x => birkhoffAverage ℝ T (g 1) (n + 1) x) μ := by
  have : (fun x => birkhoffAverage ℝ T (g 1) (n + 1) x)
      = fun x => ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g 1) (n + 1) x := rfl
  rw [this]
  exact (integrable_birkhoffSum hT (hint 1) (n + 1)).const_mul _

/-- The Fatou defect `d n` is integrable. -/
private lemma integrable_fdefect (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    Integrable (fdefect (T := T) g n) μ :=
  (integrable_birkhoffAverage_one hT hint n).sub (integrable_cdiv hint n)

/-- The integral of the Fatou defect: `∫ d n = ∫ g 1 − a_{n+1}/(n+1)`. -/
private lemma integral_fdefect (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) (n : ℕ) :
    ∫ x, fdefect (T := T) g n x ∂μ
      = (∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1) := by
  have hba := integrable_birkhoffAverage_one hT hint n
  have hcdiv := integrable_cdiv hint n
  have hfeq : (∫ x, fdefect (T := T) g n x ∂μ)
      = ∫ x, (birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x) ∂μ := rfl
  rw [hfeq, integral_sub hba hcdiv, ProbabilityTheory.integral_birkhoffAverage_eq hT (hint 1)]
  congr 1
  have hcd : (∫ x, cdiv g n x ∂μ) = ∫ x, g (n + 1) x / ((n : ℝ) + 1) ∂μ := rfl
  rw [hcd, integral_div]

/-- **Fatou core.** A.e. the `ℝ≥0∞`-`liminf` of `ENNReal.ofReal (d n x)` is finite. From this
finiteness both `⊥ < limsup (ecdiv)` and `Integrable f₊` follow. -/
private lemma ae_liminf_ofReal_fdefect_lt_top [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop ∂μ < ⊤ := by
  -- Measurable representatives for `fdefect n`, used in Fatou.
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  -- A measurable model of `ofReal (fdefect g n)`.
  set F : ℕ → X → ℝ := fun n x =>
    birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / (n + 1) with hFdef
  have hFm : ∀ n, Measurable (fun x => ENNReal.ofReal (F n x)) := by
    intro n
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.sub ?_ ((hg₀m (n + 1)).div_const _)
    change Measurable (fun x ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g₀ 1) (n + 1) x)
    exact (measurable_birkhoffSum hTm (hg₀m 1) (n + 1)).const_mul _
  -- `F n =ᵐ fdefect g n` for all `n` simultaneously.
  have hFeq : ∀ᵐ x ∂μ, ∀ n, ENNReal.ofReal (F n x) = ENNReal.ofReal (fdefect (T := T) g n x) := by
    have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g n x = g₀ n x := ae_all_iff.2 hgg₀
    have hbs : ∀ᵐ x ∂μ, ∀ n : ℕ,
        birkhoffSum T (g 1) (n + 1) x = birkhoffSum T (g₀ 1) (n + 1) x :=
      ae_all_iff.2 (fun n =>
        hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq (hgg₀ 1) (n + 1))
    filter_upwards [hall, hbs] with x hx hxbs
    intro n
    congr 1
    have hba : birkhoffAverage ℝ T (g₀ 1) (n + 1) x = birkhoffAverage ℝ T (g 1) (n + 1) x := by
      simp only [birkhoffAverage, smul_eq_mul]
      rw [hxbs n]
    change birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / ((n : ℝ) + 1)
      = birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x
    rw [hba]
    simp only [cdiv]
    rw [hx (n + 1)]
  -- Fatou for the measurable model.
  have hFatou : ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ
      ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
    lintegral_liminf_le hFm
  -- The `liminf` integrand agrees a.e. with the one we want.
  have hlhs : ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (F n x)) atTop ∂μ
      = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hFeq] with x hx
    exact congrArg (fun s => Filter.liminf s atTop) (funext hx)
  rw [hlhs] at hFatou
  -- Compute `∫⁻ ofReal (F n) = ofReal (∫ d n) = ofReal (∫ g 1 − a_{n+1}/(n+1))`.
  have hintF : ∀ n, ∫⁻ x, ENNReal.ofReal (F n x) ∂μ
      = ENNReal.ofReal ((∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1)) := by
    intro n
    have heq : (fun x => ENNReal.ofReal (F n x)) =ᵐ[μ]
        fun x => ENNReal.ofReal (fdefect (T := T) g n x) := by
      filter_upwards [hFeq] with x hx; exact hx n
    rw [lintegral_congr_ae heq,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_fdefect hT hint n)
        (Filter.Eventually.of_forall (fdefect_nonneg hsub n)),
      integral_fdefect hT hint n]
  simp only [hintF] at hFatou
  -- The `liminf` of the RHS is `ofReal (∫ g 1 − γ) < ∞`.
  obtain ⟨γ, hγ⟩ := exists_fekete hT hsub hint hbdd
  have hconv : Tendsto (fun n => ENNReal.ofReal
      ((∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1))) atTop
      (𝓝 (ENNReal.ofReal ((∫ x, g 1 x ∂μ) - γ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hγ)
  have hrhs : Filter.liminf (fun n => ENNReal.ofReal
      ((∫ x, g 1 x ∂μ) - (∫ x, g (n + 1) x ∂μ) / (n + 1))) atTop
      = ENNReal.ofReal ((∫ x, g 1 x ∂μ) - γ) := hconv.liminf_eq
  rw [hrhs] at hFatou
  exact lt_of_le_of_lt hFatou ENNReal.ofReal_lt_top

/-- A.e. measurability of the `ℝ≥0∞`-`liminf` of the Fatou defect (for `ae_lt_top'`). -/
private lemma aemeasurable_liminf_ofReal_fdefect [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hint : ∀ n, Integrable (g n) μ) :
    AEMeasurable (fun x => Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop)
      μ := by
  set g₀ : ℕ → X → ℝ := fun n => (hint n).1.mk with hg₀def
  have hg₀m : ∀ n, Measurable (g₀ n) := fun n => (hint n).1.measurable_mk
  have hgg₀ : ∀ n, g n =ᵐ[μ] g₀ n := fun n => (hint n).1.ae_eq_mk
  set F : ℕ → X → ℝ := fun n x =>
    birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / (n + 1) with hFdef
  have hFm : ∀ n, Measurable (fun x => ENNReal.ofReal (F n x)) := by
    intro n
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.sub ?_ ((hg₀m (n + 1)).div_const _)
    change Measurable (fun x ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum T (g₀ 1) (n + 1) x)
    exact (measurable_birkhoffSum hTm (hg₀m 1) (n + 1)).const_mul _
  refine ⟨fun x => Filter.liminf (fun n => ENNReal.ofReal (F n x)) atTop,
    Measurable.liminf hFm, ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, g n x = g₀ n x := ae_all_iff.2 hgg₀
  have hbs : ∀ᵐ x ∂μ, ∀ n : ℕ,
      birkhoffSum T (g 1) (n + 1) x = birkhoffSum T (g₀ 1) (n + 1) x :=
    ae_all_iff.2 (fun n =>
      hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq (hgg₀ 1) (n + 1))
  filter_upwards [hall, hbs] with x hx hxbs
  refine congrArg (fun s => Filter.liminf s atTop) (funext fun n => ?_)
  have hFval : F n x = fdefect (T := T) g n x := by
    have hba : birkhoffAverage ℝ T (g₀ 1) (n + 1) x = birkhoffAverage ℝ T (g 1) (n + 1) x := by
      simp only [birkhoffAverage, smul_eq_mul]; rw [hxbs n]
    change birkhoffAverage ℝ T (g₀ 1) (n + 1) x - g₀ (n + 1) x / ((n : ℕ) + 1 : ℝ)
      = birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x
    rw [hba]
    simp only [cdiv]
    rw [hx (n + 1)]
  rw [hFval]

/-- **Fatou step, pointwise.** A.e. the `ℝ≥0∞`-`liminf` of the Fatou defect is finite. -/
private lemma ae_liminf_fdefect_lt_top [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop < ⊤ :=
  ae_lt_top' (aemeasurable_liminf_ofReal_fdefect hT hTm hint)
    (ae_liminf_ofReal_fdefect_lt_top hT hTm hsub hint hbdd).ne

/-- A.e. the `EReal` limsup of the normalized cocycle is bounded below by
`⊥`: the Fatou defect cannot tend to `+∞`, so the cocycle cannot tend to `−∞`. -/
lemma ae_bot_lt_ereal_limsup [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, (⊥ : EReal) < Filter.limsup (fun n => ecdiv g n x) atTop := by
  filter_upwards [ae_liminf_fdefect_lt_top hT hTm hsub hint hbdd,
    tendsto_birkhoffAverage_ae hT (hint 1)] with x hfin hBconv
  -- `liminf (ofReal d_n) < ⊤`: choose a finite ceiling `C` with `liminf < C`.
  obtain ⟨C, hC1, hC2⟩ := exists_between hfin
  -- Frequently `ofReal (d_n) < C`.
  have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal (fdefect (T := T) g n x) < C :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hC1
  -- Hence frequently `d_n < C.toReal`, i.e. `cdiv ≥ A_{n+1} − C.toReal`.
  have hBshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop
      (𝓝 ((μ[g 1 | MeasurableSpace.invariants T]) x)) :=
    hBconv.comp (tendsto_add_atTop_nat 1)
  set B : ℝ := (μ[g 1 | MeasurableSpace.invariants T]) x with hBdef
  -- Eventually `A_{n+1} x > B − 1`.
  have hev : ∀ᶠ n in atTop, B - 1 < birkhoffAverage ℝ T (g 1) (n + 1) x := by
    have := hBshift.eventually (eventually_gt_nhds (show B - 1 < B by linarith))
    exact this
  -- Frequently `cdiv g n x > B − 1 − C.toReal`.
  set K : ℝ := B - 1 - C.toReal with hKdef
  have hKfreq : ∃ᶠ n in atTop, K ≤ cdiv g n x := by
    refine (hfreq.and_eventually hev).mono ?_
    rintro n ⟨hlt, hgt⟩
    -- `ofReal (d_n) < C ⟹ d_n < C.toReal` (since `d_n ≥ 0`).
    have hdlt : fdefect (T := T) g n x < C.toReal := by
      by_contra hge
      rw [not_lt] at hge
      have : C ≤ ENNReal.ofReal (fdefect (T := T) g n x) := by
        rw [← ENNReal.ofReal_toReal hC2.ne]
        exact ENNReal.ofReal_le_ofReal hge
      exact absurd hlt (not_lt.2 this)
    -- `cdiv = A_{n+1} − d_n`.
    have hcd : cdiv g n x = birkhoffAverage ℝ T (g 1) (n + 1) x - fdefect (T := T) g n x := by
      simp only [fdefect]; ring
    rw [hcd, hKdef]; linarith
  -- Lift to `EReal`: frequently `↑K ≤ ecdiv`, so `↑K ≤ limsup (ecdiv)`, and `⊥ < ↑K`.
  have hKle : ((K : ℝ) : EReal) ≤ Filter.limsup (fun n => ecdiv g n x) atTop := by
    refine le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    exact hKfreq.mono fun n hn => by simpa only [ecdiv] using EReal.coe_le_coe_iff.2 hn
  exact lt_of_lt_of_le (EReal.bot_lt_coe K) hKle

/-- The `ℝ`-valued limsup envelope `f₊` is integrable, by the Fatou step.
Set `B := μ[g 1 | invariants T]` (integrable) and `Δ := B − f₊`. Then a.e. `0 ≤ Δ` (the
envelope `f₊ ≤ B`) and `Δ ≤ liminf_n (d n) =: D` (by `le_liminf_add` applied to
`A_{n+1} + (−cdiv)`, using only that `cdiv` is bounded *above*). Since `d n ≥ 0`,
`ENNReal.ofReal D = liminf_n (ENNReal.ofReal (d n))` (`Monotone.map_liminf_of_continuousAt`),
so `∫⁻ ofReal Δ ≤ ∫⁻ liminf (ofReal d_n) < ∞` (the Fatou core
`ae_liminf_ofReal_fdefect_lt_top`). Hence `Δ` is integrable and `f₊ = B − Δ` is integrable.
This is a *direct* Fatou proof, independent of `ae_tendsto_cdiv` (no circularity), and — crucially
— it never assumes `cdiv` is bounded below (which only follows after the stopping-time lemma). -/
lemma int_limsup_div_integrable_aux [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    Integrable (fun x => Filter.limsup (fun n => cdiv g n x) atTop) μ := by
  set B : X → ℝ := fun x => (μ[g 1 | MeasurableSpace.invariants T]) x with hBdef
  have hBint : Integrable B μ := integrable_condExp
  set fp : X → ℝ := fun x => Filter.limsup (fun n => cdiv g n x) atTop with hfpdef
  -- `Δ x := B x − f₊ x`. It suffices to show `Δ` is integrable, since `f₊ = B − Δ`.
  set Δ : X → ℝ := fun x => B x - fp x with hΔdef
  suffices hΔ : Integrable Δ μ by
    have : (fun x => fp x) = fun x => B x - Δ x := by funext x; simp only [hΔdef]; ring
    rw [hfpdef] at this ⊢
    rw [this]; exact hBint.sub hΔ
  -- `Δ` is AEMeasurable.
  have hfpm : AEMeasurable fp μ := aemeasurable_limsup_div (μ := μ) hint
  have hΔm : AEMeasurable Δ μ := hBint.aestronglyMeasurable.aemeasurable.sub hfpm
  -- Pointwise on a good set: `0 ≤ Δ x ≤ liminf (defect)` and `ofReal (Δ x) ≤ liminf (ofReal d)`.
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (Δ x)
      ≤ Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop := by
    filter_upwards [tendsto_birkhoffAverage_ae hT (hint 1),
      ae_bddAbove_cdiv hT hsub hint,
      ae_liminf_fdefect_lt_top hT hTm hsub hint hbdd] with x hBconv hba hfdlt
    have hBshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop (𝓝 (B x)) :=
      hBconv.comp (tendsto_add_atTop_nat 1)
    -- boundedness of `cdiv` (above, from `hba`) and of `A_{n+1}` (converges).
    have hbA : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) :=
      hba.isBoundedUnder_of_range
    -- bounded below of `fdefect` (it is `≥ 0`).
    have hbdef : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => fdefect (T := T) g n x) := by
      refine ⟨0, ?_⟩
      simp only [eventually_map]
      exact Eventually.of_forall fun n => fdefect_nonneg hsub n x
    -- cobounded `(· ≥ ·)`: from `liminf (ofReal d) < ⊤`, frequently `d n ≤ C.toReal`.
    have hcobdef : Filter.IsCoboundedUnder (· ≥ ·) atTop (fun n => fdefect (T := T) g n x) := by
      obtain ⟨C, hC1, hC2⟩ := exists_between hfdlt
      refine IsCoboundedUnder.of_frequently_le (a := C.toReal) ?_
      have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal (fdefect (T := T) g n x) < C :=
        frequently_lt_of_liminf_lt (by isBoundedDefault) hC1
      refine hfreq.mono fun n hn => ?_
      by_contra hge
      rw [not_le] at hge
      exact absurd hn (not_lt.2 (le_trans (by
        rw [← ENNReal.ofReal_toReal hC2.ne]
        exact ENNReal.ofReal_le_ofReal hge.le) (le_refl _)))
    -- `D := liminf fdefect`; `B − f₊ ≤ D` via the eventual bound `fdefect ≥ B − f₊ − 2δ`.
    set D : ℝ := Filter.liminf (fun n => fdefect (T := T) g n x) atTop with hDdef
    have hkey : B x - fp x ≤ D := by
      have hstep : ∀ δ : ℝ, 0 < δ → B x - fp x - 2 * δ ≤ D := by
        intro δ hδ
        refine le_liminf_of_le hcobdef ?_
        -- Eventually `A_{n+1} > B x − δ` and `cdiv n < f₊ x + δ`.
        have hev1 : ∀ᶠ n in atTop, B x - δ < birkhoffAverage ℝ T (g 1) (n + 1) x :=
          hBshift.eventually (eventually_gt_nhds (by linarith))
        have hev2 : ∀ᶠ n in atTop, cdiv g n x < fp x + δ :=
          eventually_lt_of_limsup_lt (show Filter.limsup (fun n => cdiv g n x) atTop < fp x + δ
            from by have : Filter.limsup (fun n => cdiv g n x) atTop = fp x := rfl; linarith) hbA
        filter_upwards [hev1, hev2] with n h1 h2
        have : fdefect (T := T) g n x = birkhoffAverage ℝ T (g 1) (n + 1) x - cdiv g n x := rfl
        rw [this]; linarith
      by_contra hlt
      rw [not_le] at hlt
      have := hstep ((B x - fp x - D) / 4) (by linarith)
      linarith
    have hmap : ENNReal.ofReal D
        = Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop := by
      have := ENNReal.ofReal_mono.map_liminf_of_continuousAt
        (a := fun n => fdefect (T := T) g n x)
        (ENNReal.continuous_ofReal.continuousAt) hcobdef hbdef
      simpa only [hDdef, Function.comp_def] using this
    calc ENNReal.ofReal (Δ x) = ENNReal.ofReal (B x - fp x) := rfl
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal hkey
      _ = _ := hmap
  -- `Δ ≥ 0` a.e. (envelope `f₊ ≤ B`).
  have hΔnn : 0 ≤ᵐ[μ] Δ := by
    filter_upwards [tendsto_birkhoffAverage_ae hT (hint 1),
      ae_bot_lt_ereal_limsup hT hTm hsub hint hbdd] with x hBconv hbot
    have hBshift : Tendsto (fun n : ℕ => birkhoffAverage ℝ T (g 1) (n + 1) x) atTop (𝓝 (B x)) :=
      hBconv.comp (tendsto_add_atTop_nat 1)
    -- cobounded `(· ≤ ·)` of `cdiv` from `⊥ < limsup (ecdiv)` (frequently `cdiv ≥ K`).
    have hcob : Filter.IsCoboundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) := by
      obtain ⟨K, _, hK2⟩ := EReal.lt_iff_exists_real_btwn.1 hbot
      refine IsCoboundedUnder.of_frequently_ge (a := K) ?_
      have hfreq : ∃ᶠ n in atTop, (K : EReal) < ecdiv g n x :=
        frequently_lt_of_lt_limsup (by isBoundedDefault) hK2
      refine hfreq.mono fun n hn => ?_
      simpa only [ecdiv] using (EReal.coe_lt_coe_iff.1 hn).le
    have hle : fp x ≤ B x := by
      have hstep : ∀ δ : ℝ, 0 < δ → fp x ≤ B x + δ := by
        intro δ hδ
        refine limsup_le_of_le hcob ?_
        have hAle : ∀ᶠ n in atTop, birkhoffAverage ℝ T (g 1) (n + 1) x < B x + δ :=
          hBshift.eventually (eventually_lt_nhds (by linarith))
        filter_upwards [hAle] with n hn
        exact le_of_lt (lt_of_le_of_lt (cdiv_le_birkhoffAverage hsub n x) hn)
      by_contra hlt
      rw [not_le] at hlt
      have := hstep ((fp x - B x) / 2) (by linarith)
      linarith
    change (0 : ℝ) ≤ Δ x
    simp only [hΔdef]
    linarith
  -- Finite lintegral: `∫⁻ ofReal Δ ≤ ∫⁻ liminf (ofReal d) < ∞`.
  have hfin : ∫⁻ x, ENNReal.ofReal (Δ x) ∂μ < ⊤ := by
    calc ∫⁻ x, ENNReal.ofReal (Δ x) ∂μ
        ≤ ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (fdefect (T := T) g n x)) atTop ∂μ :=
          lintegral_mono_ae hpt
      _ < ⊤ := ae_liminf_ofReal_fdefect_lt_top hT hTm hsub hint hbdd
  -- Conclude `Integrable Δ`.
  rw [Integrable, hasFiniteIntegral_iff_ofReal hΔnn]
  exact ⟨hΔm.aestronglyMeasurable, hfin⟩

end ProbabilityTheory.Kingman
