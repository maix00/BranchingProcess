/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
module

public import Probability.Ergodic.Kingman.Basic
import Probability.Ergodic.Kingman.EnvelopeInvariant
import all Probability.Ergodic.Kingman.Lemmas.BlockSqueeze
import all Probability.Ergodic.Kingman.Lemmas.FatouEnvelope

/-!
# Kingman's subadditive ergodic theorem

The core a.e.-existence of an integrable limit, the a.e. `T`-invariance and integrability of the
envelopes, the hard direction `limsup ≤ liminf` a.e., and the final assembly of **Kingman's
subadditive ergodic theorem**: for a measure-preserving `T` and an integrable subadditive cocycle
whose normalized integrals are bounded below, `gₙ / n` converges `μ`-a.e. to a `T`-invariant
integrable limit; under ergodicity the limit is a.e. constant.

The reusable cocycle interface is in `Probability.Ergodic.Kingman.Basic`; the integral Fekete
step is in `Fekete`. The proof support is grouped under `Lemmas/`: Fatou-envelope estimates in
`Lemmas/FatouEnvelope`, Derriennic estimates in `Lemmas/Derriennic`, the companion-cocycle reduction in
`Lemmas/Companion`, the pointwise envelope comparison private to `EnvelopeInvariant.lean`, and
block-squeeze assembly in `Lemmas/BlockSqueeze`. The general
real-valued filter lemmas for vanishing perturbations are in `Order.Filter.LiminfLimsup`.

## Public declarations

* `ProbabilityTheory.Kingman.ae_tendsto_cdiv`: for a finite measure-preserving system and an
  integrable subadditive cocycle whose normalized integrals are bounded below, there is an
  integrable `G` such that `g (n+1) x / (n+1) → G x` for almost every `x`.
* `ProbabilityTheory.tendsto_kingman`: under the same assumptions,
  `g n x / n → G x` almost everywhere for a `T`-invariant integrable `G`.
* `ProbabilityTheory.tendsto_kingman_ergodic`: when `μ` is a probability measure and `T` is
  ergodic, there is a constant `c` such that `g n x / n → c` almost everywhere.

Under the measure-preserving and integrability hypotheses in the declarations,
the normalized cocycle converges almost everywhere to an invariant integrable
function, which is constant almost everywhere in the ergodic case:

\[\begin{aligned}
\frac{g_{n+1}(x)}{n+1}&\longrightarrow G(x)
  &&\text{for }\mu\text{-almost every }x,\\
G\circ T&=G\quad\mu\text{-almost everywhere},\\
T\text{ ergodic}&\Longrightarrow
  \exists c\in\mathbb R,\quad
  \frac{g_n(x)}n\longrightarrow c
  &&\text{for }\mu\text{-almost every }x.
\end{aligned}\]

## References

* J. F. C. Kingman, *The ergodic theory of subadditive stochastic processes*,
  Theorem 1, J. Roy. Statist. Soc. Ser. B **30** (1968), 499–510, DOI
  10.1111/j.2517-6161.1968.tb00749.x.
* Y. Katznelson and B. Weiss, *A simple proof of some ergodic theorems*,
  the unnumbered statement and proof of Kingman's subadditive ergodic theorem,
  pp. 293–296, Israel J. Math. **42** (1982), 291–296, DOI
  10.1007/BF02761409.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

omit [MeasurableSpace X] in
private theorem tendsto_kingman_reindex {g : ℕ → X → ℝ} {x : X} {L : ℝ} :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 L) ↔
      Tendsto (fun n : ℕ => g (n + 1) x / (n + 1)) atTop (𝓝 L) := by
  rw [← tendsto_add_atTop_iff_nat (f := fun n : ℕ => (n : ℝ)⁻¹ * g n x) 1]
  refine tendsto_congr (fun n => ?_)
  push_cast
  rw [div_eq_inv_mul]

/-! ### The Kingman core: a.e. existence of an integrable limit -/

/-- **Kingman core.** The normalized cocycle `g (n+1) x / (n+1)`
converges, for `μ`-a.e. `x`, to the value `G x` of some integrable `G`. This is the
limit-existence stage of Kingman's theorem:

* a.e. **convergence** (the stopping-time / greedy block partition, Katznelson–Weiss); and
* **integrability** of the limit (the Fatou step).

The a.e. lower boundedness, real-valued envelope integrability, and limsup/liminf comparison
used in the final assembly follow from this limit. The liminf-envelope invariance is exposed as
the auxiliary theorem `Kingman.liminf_div_comp_ae` in `EnvelopeInvariant.lean`.

The proof works with the `EReal`-valued `limsup`/`liminf` to retain possible infinite limits:
the `ℝ≥0∞` Fatou step (`ae_bot_lt_ereal_limsup`, `int_limsup_div_integrable_aux`)
gives `limsup > ⊥` a.e. and the integrability; the stopping-time lemma
`ae_ereal_liminf_eq_limsup` gives `liminf = limsup`; together with the envelope
`limsup ≤ ↑B < ⊤` they force a finite a.e. limit `e.toReal`. -/
theorem ae_tendsto_cdiv [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, Integrable G μ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => cdiv g n x) atTop (𝓝 (G x)) := by
  -- `G := f₊` (the `ℝ`-valued limsup), integrable by the Fatou step.
  refine ⟨fun x => Filter.limsup (fun n => cdiv g n x) atTop,
    int_limsup_div_integrable_aux hT hTm hsub hint hbdd, ?_⟩
  -- On the good set: `⊥ < e ≤ ↑B < ⊤` and `liminf = limsup = e`, so `cdiv → e.toReal = f₊ x`.
  filter_upwards [ae_ereal_limsup_le_condExp hT hsub hint,
    ae_bot_lt_ereal_limsup hT hTm hsub hint hbdd,
    ae_ereal_liminf_eq_limsup hT hsub hint hbdd] with x hupper hbot heq
  set e : EReal := Filter.limsup (fun n => ecdiv g n x) atTop with hedef
  -- Finiteness of `e`.
  have hetop : e ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_lt_top _).ne hupper
  have hebot : e ≠ ⊥ := hbot.ne'
  -- `ecdiv → e` from `liminf = limsup = e` (EReal is a complete linear order).
  have htend_e : Tendsto (fun n => ecdiv g n x) atTop (𝓝 e) :=
    tendsto_of_liminf_eq_limsup heq rfl
  -- Transfer to `ℝ`: `cdiv → e.toReal`.
  have hcoe : e = ((e.toReal : ℝ) : EReal) := (EReal.coe_toReal hetop hebot).symm
  have htend_r : Tendsto (fun n => cdiv g n x) atTop (𝓝 e.toReal) := by
    rw [← EReal.tendsto_coe]
    have : (fun n => ((cdiv g n x : ℝ) : EReal)) = fun n => ecdiv g n x := rfl
    rw [this, ← hcoe]
    exact htend_e
  -- `f₊ x = e.toReal` since the sequence converges.
  have hfp : Filter.limsup (fun n => cdiv g n x) atTop = e.toReal := htend_r.limsup_eq
  rw [hfp]
  exact htend_r

/-- A.e. the range of `cdiv g · x` is bounded below: a convergent sequence is bounded
(derived from `ae_tendsto_cdiv`). -/
private theorem ae_bddBelow_cdiv [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, BddBelow (Set.range fun n : ℕ => cdiv g n x) := by
  obtain ⟨G, _, hG⟩ := ae_tendsto_cdiv hT hT.measurable hsub hint hbdd
  filter_upwards [hG] with x hx
  exact hx.bddBelow_range

/-! ### Integrability of the limsup envelope -/

/-- **`Integrable f₊`.** The limsup envelope `f₊ x = limsup_n cdiv g n x` is integrable:
on the a.e. set where `cdiv g · x` converges to `G x` (`ae_tendsto_cdiv`), the limsup equals
`G x`, and `G` is integrable. -/
private theorem int_limsup_div_integrable [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    Integrable (fun x => Filter.limsup (fun n => cdiv g n x) atTop) μ := by
  obtain ⟨G, hGint, hG⟩ := ae_tendsto_cdiv hT hT.measurable hsub hint hbdd
  refine (integrable_congr ?_).mpr hGint
  filter_upwards [hG] with x hx
  exact hx.limsup_eq

/-! ### The hard direction: `limsup ≤ liminf` almost everywhere -/

/-- **`limsup ≤ liminf` a.e.** For a.e. `x` the limsup of the normalized cocycle is dominated
by its liminf. Derived from `ae_tendsto_cdiv`: where the sequence converges, both equal the
limit. (The deep content is in `ae_tendsto_cdiv`; this is a soft corollary.) -/
private theorem ae_limsup_le_liminf_div [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hTm : Measurable T) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∀ᵐ x ∂μ, Filter.limsup (fun n => cdiv g n x) atTop
      ≤ Filter.liminf (fun n => cdiv g n x) atTop := by
  obtain ⟨G, _, hG⟩ := ae_tendsto_cdiv hT hTm hsub hint hbdd
  filter_upwards [hG] with x hx
  exact le_of_eq (hx.limsup_eq.trans hx.liminf_eq.symm)


end ProbabilityTheory.Kingman

namespace ProbabilityTheory

open ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-! ### Assembly -/

/-- **Kingman's subadditive ergodic theorem.** For a measure-preserving `T` and
an integrable subadditive cocycle `g` whose normalized integrals are bounded below,
`gₙ / n` converges `μ`-a.e. to a `T`-invariant integrable limit `G`. -/
theorem tendsto_kingman [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ G : X → ℝ, (G ∘ T =ᵐ[μ] G) ∧ Integrable G μ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 (G x))) := by
  -- The a.e. limit is the liminf envelope `f₋`.
  set fm : X → ℝ := fun x => Filter.liminf (fun n => cdiv g n x) atTop with hfmdef
  set fp : X → ℝ := fun x => Filter.limsup (fun n => cdiv g n x) atTop with hfpdef
  -- `f₋ =ᵐ f₊` (`ae_limsup_le_liminf_div` + `liminf_le_limsup`, on the a.e.-bounded set).
  have heq : fm =ᵐ[μ] fp := by
    filter_upwards [ae_limsup_le_liminf_div hT hT.measurable hsub hint hbdd,
      ae_bddAbove_cdiv hT hsub hint, ae_bddBelow_cdiv hT hsub hint hbdd] with x hle hba hbb
    have hbA : IsBoundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) := hba.isBoundedUnder_of_range
    have hbB : IsBoundedUnder (· ≥ ·) atTop (fun n => cdiv g n x) := hbb.isBoundedUnder_of_range
    exact le_antisymm (Filter.liminf_le_limsup hbA hbB) hle
  refine ⟨fm, ?_, ?_, ?_⟩
  · -- `f₋ ∘ T =ᵐ f₋`: directly the liminf-envelope invariance (`liminf_div_comp_ae`).
    exact liminf_div_comp_ae hT hsub hint
      (ae_bddBelow_cdiv hT hsub hint hbdd)
  · -- `Integrable f₋`: `f₋ =ᵐ f₊` and `f₊` integrable (`int_limsup_div_integrable`).
    have hfp_int : Integrable fp μ := int_limsup_div_integrable hT hsub hint hbdd
    exact (integrable_congr heq).mpr hfp_int
  · -- Pointwise convergence of `cdiv g · x` to `f₋ x`, then reindex.
    filter_upwards [ae_limsup_le_liminf_div hT hT.measurable hsub hint hbdd,
      ae_bddAbove_cdiv hT hsub hint, ae_bddBelow_cdiv hT hsub hint hbdd] with x hle hba hbb
    have hbA : IsBoundedUnder (· ≤ ·) atTop (fun n => cdiv g n x) := hba.isBoundedUnder_of_range
    have hbB : IsBoundedUnder (· ≥ ·) atTop (fun n => cdiv g n x) := hbb.isBoundedUnder_of_range
    -- `f₋ x ≤ liminf` (refl) and `limsup ≤ f₋ x`, so the sequence converges to `f₋ x`.
    have htend : Tendsto (fun n => cdiv g n x) atTop (𝓝 (fm x)) :=
      tendsto_of_le_liminf_of_limsup_le (le_refl _) hle hbA hbB
    -- Reindex to the original Kingman sequence.
    rw [tendsto_kingman_reindex]
    exact htend

/-- **Kingman, ergodic case**: under ergodicity the a.e. limit is a single constant.
(That constant is the Fekete infimum `⨅ n, (∫ g_{n+1})/(n+1)`; the statement here asserts
only a.e.-constancy, which is what the multiplicative ergodic theorem consumes.) -/
theorem tendsto_kingman_ergodic
    [IsProbabilityMeasure μ] (hT : Ergodic T μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * g n x) atTop (𝓝 c) := by
  have hmp : MeasurePreserving T μ μ := hT.toMeasurePreserving
  -- Kingman gives a `T`-invariant integrable limit `G`.
  obtain ⟨G, hGinv, hGint, hGconv⟩ := tendsto_kingman hmp hsub hint hbdd
  -- Ergodicity forces `G` a.e. constant.
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hGint.aestronglyMeasurable hGinv
  refine ⟨c, ?_⟩
  filter_upwards [hGconv, hc] with x hx hcx
  have hcx' : G x = c := hcx
  rwa [hcx'] at hx

end ProbabilityTheory
