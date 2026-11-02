/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Probability.RandomMeasure.Poisson.PointFamily.Independence

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Integration

/-!
# Poisson thinning and within-piece factorization

This module computes the distribution of counts obtained by retaining marks in measurable sets.
The probability-generating identity for a finite piece yields Poisson thinning and independence
for disjoint sets, including finite families of pairwise disjoint sets.

## Public declarations

- `thinnedCount` counts the marks of piece $k$ that fall in $A$;
  `measurable_thinnedCount` gives its measurability.
- `integral_pieceProd_eq_exp` gives the piece probability-generating identity
  $\mathbb E\left[\prod_{n<K_k}w(X_{k,n})\right]
    =\exp\left((m(\operatorname{prmPiece}(m,k))).toReal
      \left(\int w\,d\operatorname{prmPieceLaw}(m,k)-1\right)\right)$
  for measurable complex-valued $w$ satisfying $\|w(x)\|\leq 1$ for every $x$.
- `map_thinnedCount` states that, for measurable $A$, the retained count has law
  `poissonMeasure ((m (prmPiece m k ∩ A)).toNNReal)`.
- `indepFun_thinnedCount_thinnedCount` gives independence for disjoint measurable sets within one
  piece; `charFunDual_prod_thinnedCount` gives the two-set characteristic-function factorization.
  For a finite disjoint family and weights satisfying $\|z_i\|\leq1$,
  `integral_prod_pow_thinnedCount` and `charFunDual_pi_thinnedCount` give the joint generating and
  characteristic-function identities, and `iIndepFun_thinnedCount` concludes mutual independence.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-! ### Thinning and within-piece factorization

The number of piece-`k` points that land in a set `A` is the *thinned count* `thinnedCount K X A k`.
The engine behind its distribution is the **probability-generating-function identity**
`E[∏_{n < K k} w (X k n)] = exp (m (piece k) · (∫ w d(pieceLaw k) − 1))` for any bounded measurable
`w : E → ℂ` (`integral_pieceProd_eq_exp`), proved by the same cell-partition over `{K k = j}` used
for Campbell's formula, this time with a bounded integrand. Feeding in the indicator-shaped weights
`w x = z ^ 1_A(x)` and reading the resulting characteristic function against
`charFun_map_cast_poissonMeasure` yields both Poisson **thinning** (`map_thinnedCount`) and the
**within-piece independence** of thinned counts on disjoint sets
(`indepFun_thinnedCount_thinnedCount`). -/

section Thinning

open Complex
open scoped NNReal

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ} {A B : Set E}

/-- **Poisson probability-generating series (complex form).** `∑ⱼ P(N = j) · wʲ = exp(λ(w − 1))` for
any complex `w`; the analytic identity behind the piece pgf identity. Re-derived here rather than
imported from the compound-Poisson development. -/
private lemma tsum_poissonMeasure_real_mul_cpow (lam : ℝ≥0) (w : ℂ) :
    ∑' j : ℕ, ((poissonMeasure lam).real {j} : ℂ) * w ^ j = Complex.exp ((lam : ℝ) * (w - 1)) := by
  have hterm : ∀ j : ℕ, ((poissonMeasure lam).real {j} : ℂ) * w ^ j
      = (Real.exp (-(lam : ℝ)) : ℂ) * (((lam : ℝ) * w) ^ j / (Nat.factorial j : ℂ)) := by
    intro j
    simp only [poissonMeasure_real_singleton]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum := NormedSpace.expSeries_div_hasSum_exp (((lam : ℝ) : ℂ) * w)
  rw [hsum.tsum_eq, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Constant-branch product of a two-valued `if`: `∏ᵢ (if p i then z else 1) = z ^ #{i : p i}`. -/
private lemma prod_ite_const {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (z : ℂ) :
    ∏ i ∈ s, (if p i then z else 1) = z ^ (s.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- Integral of a complex-constant indicator, stated as a plain product to avoid the noncanonical
`ℝ`-on-`ℂ` scalar action that `integral_indicator_const` exposes: since `Complex.real_smul` is
`rfl`, the residual `μ.real s • c` closes by definitional unfolding via `exact`. -/
private lemma integral_indicator_const_complex {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {s : Set α} (c : ℂ) (hs : MeasurableSet s) :
    ∫ x, s.indicator (fun _ => c) x ∂ν = (ν.real s : ℂ) * c := by
  rw [integral_indicator_const c hs]; exact Complex.real_smul

/-- A real linear form on `ℝ` acts by scaling: `M r = r · M 1`. -/
private lemma real_dual_apply (M : StrongDual ℝ ℝ) (r : ℝ) : M r = r * M 1 := by
  conv_rhs => rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- A linear form on `ℝ × ℝ` splits over the two coordinates: `L (x, y) = x · L(1,0) + y · L(0,1)`. -/
private lemma prod_dual_apply (L : StrongDual ℝ (ℝ × ℝ)) (x y : ℝ) :
    L (x, y) = x * (L.comp (.inl ℝ ℝ ℝ) 1) + y * (L.comp (.inr ℝ ℝ ℝ) 1) := by
  rw [← ContinuousLinearMap.comp_inl_add_comp_inr L (x, y)]
  dsimp only
  rw [real_dual_apply (L.comp (.inl ℝ ℝ ℝ)) x, real_dual_apply (L.comp (.inr ℝ ℝ ℝ)) y]

open Classical in
/-- The **thinned count**: the number of the `K k ω` points of piece `k` that land in `A`. -/
noncomputable def thinnedCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (A : Set E) (k : ℕ) (ω : Ω) :
    ℕ := ((Finset.range (K k ω)).filter fun n => X k n ω ∈ A).card

omit [Nonempty E] in
/-- The thinned count is measurable: it is a countable-index sum of the measurable point-membership
indicators, capped by the measurable count. -/
theorem measurable_thinnedCount (hK : Measurable (K k)) (hX : ∀ n, Measurable (X k n))
    (hA : MeasurableSet A) : Measurable (thinnedCount K X A k) := by
  classical
  have hcard : thinnedCount K X A k
      = fun ω => ∑ n ∈ Finset.range (K k ω), (if X k n ω ∈ A then (1 : ℕ) else 0) := by
    funext ω; rw [thinnedCount, Finset.card_filter]
  rw [hcard]
  have hp : Measurable
      fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, (if X k n p.1 ∈ A then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ =>
        Measurable.ite (hX n hA) measurable_const measurable_const
  exact hp.comp (measurable_id.prodMk hK)

/-- Each mark contributes a factor `∫ w d(pieceLaw k)`, so the product of the first `j` marks
integrates to its `j`-th power, by within-piece i.i.d. independence. -/
private lemma integral_marksProd_eq [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {w : E → ℂ} (hw : Measurable w) (j : ℕ) :
    ∫ ω, ∏ n ∈ Finset.range j, w (X k n ω) ∂μ = (∫ x, w x ∂(prmPieceLaw m k)) ^ j := by
  have hZ : iIndepFun (fun i : Fin j => X k (i : ℕ)) μ :=
    (hd.iIndepFun_point_piece k).precomp Fin.val_injective
  have hfun : (fun ω => ∏ n ∈ Finset.range j, w (X k n ω))
      = fun ω => ∏ i : Fin j, w (X k (i : ℕ) ω) := by
    funext ω; exact (Fin.prod_univ_eq_prod_range (fun n => w (X k n ω)) j).symm
  rw [hfun]
  rw [show (∫ ω, ∏ i : Fin j, w (X k (i : ℕ) ω) ∂μ)
        = ∏ i : Fin j, ∫ ω, w (X k (i : ℕ) ω) ∂μ from
      iIndepFun.integral_fun_prod_comp (f := fun _ : Fin j => w) hZ
        (fun i => (hd.measurable_point k (i : ℕ)).aemeasurable)
        (fun _ => hw.aestronglyMeasurable)]
  have heach : ∀ i : Fin j, ∫ ω, w (X k (i : ℕ) ω) ∂μ = ∫ x, w x ∂(prmPieceLaw m k) := by
    intro i
    rw [← (hd.law_point k (i : ℕ)).map_eq,
      integral_map (hd.measurable_point k (i : ℕ)).aemeasurable hw.aestronglyMeasurable]
  simp_rw [heach]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Conditional pgf factorization (complex).** On `{K k = j}`, the integral of a measurable complex
functional of the marks factors as the probability of the event times its integral. -/
private lemma setIntegral_count_marksFun_complex [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ) {ψ : (ℕ → E) → ℂ} (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ
      = (μ.real {ω | K k ω = j} : ℂ) * ∫ ω, ψ (fun n => X k n ω) ∂μ := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  have hXk_meas : Measurable (fun ω (n : ℕ) => X k n ω) :=
    Measurable.of_eval fun n => hd.measurable_point k n
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (fun n => X k n ω))
      = fun ω => (if K k ω = j then (1 : ℂ) else 0) * ψ (fun n => X k n ω) := by
    funext ω; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr]
  simp only []
  rw [show (∫ ω, (if K k ω = j then (1 : ℂ) else 0) * ψ (fun n => X k n ω) ∂μ)
        = (∫ ω, (if K k ω = j then (1 : ℂ) else 0) ∂μ) * ∫ ω, ψ (fun n => X k n ω) ∂μ from
      (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
        (f := fun c : ℕ => if c = j then (1 : ℂ) else 0) (g := ψ)
        (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
        (measurable_of_countable _).aestronglyMeasurable hψ.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℂ) else 0) ∂μ = (μ.real {ω | K k ω = j} : ℂ) := by
    have hrw : (fun ω => if K k ω = j then (1 : ℂ) else 0)
        = ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω; by_cases h : K k ω = j <;> simp [Set.mem_ofPred_eq, h]
    rw [hrw, integral_indicator_const_complex (1 : ℂ) hmeas, mul_one]
  rw [hfirst]

/-- **The piece pgf identity.** For any bounded measurable `w : E → ℂ`,
`E[∏_{n < K k} w (X k n)] = exp (m (piece k) · (∫ w d(pieceLaw k) − 1))`. Proved by conditioning on
the count `K k`: on `{K k = j}` the product is a fixed i.i.d. product integrating to
`P(K k = j) · (∫ w)ʲ`, and summing the Poisson pgf series closes it. The zero-mass piece is handled
uniformly: both sides collapse to `1`. -/
theorem integral_pieceProd_eq_exp [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {w : E → ℂ} (hw : Measurable w) (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    ∫ ω, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ
      = Complex.exp ((m (prmPiece m k)).toReal * ((∫ x, w x ∂(prmPieceLaw m k)) - 1)) := by
  classical
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_ofPred_eq]
    intro ω h1 h2; exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have hPmeas : Measurable fun ω => ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    have hp : Measurable fun p : Ω × ℕ => ∏ n ∈ Finset.range p.2, w (X k n p.1) :=
      measurable_from_prod_countable_left fun j =>
        Finset.measurable_prod (Finset.range j) fun n _ => hw.comp (hd.measurable_point k n)
    exact hp.comp (measurable_id.prodMk (hd.measurable_count k))
  have hbound : ∀ ω, ‖∏ n ∈ Finset.range (K k ω), w (X k n ω)‖ ≤ 1 := by
    intro ω
    calc ‖∏ n ∈ Finset.range (K k ω), w (X k n ω)‖
        = ∏ n ∈ Finset.range (K k ω), ‖w (X k n ω)‖ := norm_prod _ _
      _ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hbdd _)
  have hInt : Integrable (fun ω => ∏ n ∈ Finset.range (K k ω), w (X k n ω)) μ :=
    (integrable_const (1 : ℝ)).mono' hPmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hval := integral_iUnion (f := fun ω => ∏ n ∈ Finset.range (K k ω), w (X k n ω))
    hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  have hcell : ∀ j, ∫ ω in s j, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ
      = ((poissonMeasure (m (prmPiece m k)).toNNReal).real {j} : ℂ) * (∫ x, w x ∂(prmPieceLaw m k)) ^ j := by
    intro j
    have hcount : μ.real {ω | K k ω = j}
        = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} := by
      exact (hd.law_count k).measureReal_eq (p := fun n => n = j)
        (measurableSet_singleton j)
    have hψmeas : Measurable (fun y : ℕ → E => ∏ n ∈ Finset.range j, w (y n)) :=
      Finset.measurable_prod _ fun n _ => hw.comp (measurable_pi_apply n)
    have hEq : ∫ ω in s j, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ
        = ∫ ω in s j, (fun y : ℕ → E => ∏ n ∈ Finset.range j, w (y n)) (fun n => X k n ω) ∂μ := by
      refine setIntegral_congr_fun (hs_meas j) fun ω hω => ?_
      show (∏ n ∈ Finset.range (K k ω), w (X k n ω)) = ∏ n ∈ Finset.range j, w (X k n ω)
      rw [show K k ω = j from hω]
    rw [hEq, setIntegral_count_marksFun_complex hd j hψmeas, hcount]
    congr 1
    exact integral_marksProd_eq hd hw j
  simp_rw [hcell]
  exact tsum_poissonMeasure_real_mul_cpow (m (prmPiece m k)).toNNReal (∫ x, w x ∂(prmPieceLaw m k))

/-- The mass bridge for thinning: `m (piece k) · pieceLaw k (A) = m (piece k ∩ A)`. -/
private lemma toReal_mul_real_prmPieceLaw (hA : MeasurableSet A) :
    (m (prmPiece m k)).toReal * (prmPieceLaw m k).real A = (m (prmPiece m k ∩ A)).toReal := by
  by_cases h : m (prmPiece m k) = 0
  · have h2 : m (prmPiece m k ∩ A) = 0 := measure_mono_null Set.inter_subset_left h
    rw [h, ENNReal.toReal_zero, zero_mul, h2, ENNReal.toReal_zero]
  · rw [prmPieceLaw_eq_smul_restrict_of_ne_zero h, measureReal_def, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨h, measure_prmPiece_lt_top.ne⟩), one_mul,
      Set.inter_comm]

/-- The pgf identity at the indicator weight `w x = z ^ 1_A(x)`:
`E[z ^ (thinnedCount A)] = exp (m (piece k ∩ A) · (z − 1))`, for `‖z‖ ≤ 1`. -/
private lemma integral_pow_thinnedCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∫ ω, z ^ (thinnedCount K X A k ω) ∂μ
      = Complex.exp ((m (prmPiece m k ∩ A)).toReal * (z - 1)) := by
  classical
  set w : E → ℂ := fun x => if x ∈ A then z else 1 with hw_def
  have hwmeas : Measurable w := Measurable.ite hA measurable_const measurable_const
  have hwbdd : ∀ x, ‖w x‖ ≤ 1 := by
    intro x; simp only [hw_def]; split_ifs with hx
    · exact hz
    · simp
  have hprod : ∀ ω, z ^ (thinnedCount K X A k ω) = ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    simp only [hw_def]
    rw [prod_ite_const (Finset.range (K k ω)) (fun n => X k n ω ∈ A) z, thinnedCount]
  simp_rw [hprod]
  rw [integral_pieceProd_eq_exp hd hwmeas hwbdd]
  congr 1
  have hint : ∫ x, w x ∂(prmPieceLaw m k) = 1 + (z - 1) * ((prmPieceLaw m k).real A) := by
    have hwrw : w = fun x => (1 : ℂ) + A.indicator (fun _ => z - 1) x := by
      funext x
      by_cases hx : x ∈ A
      · simp only [hw_def, Set.indicator_of_mem hx, ite_eq_left hx]; ring
      · simp only [hw_def, Set.indicator_of_notMem hx, ite_eq_right hx]; ring
    have hone : ∫ _ : E, (1 : ℂ) ∂(prmPieceLaw m k) = 1 := by simp
    rw [hwrw, integral_add (integrable_const 1) ((integrable_const (z - 1)).indicator hA),
      hone, integral_indicator_const_complex (z - 1) hA]
    ring
  rw [hint]
  have halg : ((m (prmPiece m k)).toReal : ℂ) * ((1 + (z - 1) * ((prmPieceLaw m k).real A)) - 1)
      = (((m (prmPiece m k)).toReal * (prmPieceLaw m k).real A : ℝ) : ℂ) * (z - 1) := by
    push_cast; ring
  rw [halg, toReal_mul_real_prmPieceLaw hA]

/-- The pgf identity at the disjoint two-indicator weight, feeding the within-piece independence:
`E[z₁ ^ (thinnedCount A) · z₂ ^ (thinnedCount B)]` factorizes across the two exponentials, the cross
term vanishing by `Disjoint A B`. -/
private lemma integral_pow_thinnedCount_mul [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (z₁ z₂ : ℂ) (hz₁ : ‖z₁‖ ≤ 1) (hz₂ : ‖z₂‖ ≤ 1) :
    ∫ ω, z₁ ^ (thinnedCount K X A k ω) * z₂ ^ (thinnedCount K X B k ω) ∂μ
      = Complex.exp ((m (prmPiece m k ∩ A)).toReal * (z₁ - 1))
        * Complex.exp ((m (prmPiece m k ∩ B)).toReal * (z₂ - 1)) := by
  classical
  set w : E → ℂ := fun x => (if x ∈ A then z₁ else 1) * (if x ∈ B then z₂ else 1) with hw_def
  have hwmeas : Measurable w :=
    (Measurable.ite hA measurable_const measurable_const).mul
      (Measurable.ite hB measurable_const measurable_const)
  have hwbdd : ∀ x, ‖w x‖ ≤ 1 := by
    intro x
    rw [hw_def, norm_mul]
    have hA : ‖if x ∈ A then z₁ else 1‖ ≤ 1 := by
      split_ifs with hx
      · exact hz₁
      · simp
    have hB : ‖if x ∈ B then z₂ else 1‖ ≤ 1 := by
      split_ifs with hx
      · exact hz₂
      · simp
    exact (mul_le_of_le_one_left (norm_nonneg _) hA).trans hB
  have hprod : ∀ ω, z₁ ^ (thinnedCount K X A k ω) * z₂ ^ (thinnedCount K X B k ω)
      = ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    simp only [hw_def, Finset.prod_mul_distrib]
    rw [prod_ite_const (Finset.range (K k ω)) (fun n => X k n ω ∈ A) z₁,
      prod_ite_const (Finset.range (K k ω)) (fun n => X k n ω ∈ B) z₂, thinnedCount, thinnedCount]
  simp_rw [hprod]
  rw [integral_pieceProd_eq_exp hd hwmeas hwbdd, ← Complex.exp_add]
  congr 1
  have hint : ∫ x, w x ∂(prmPieceLaw m k)
      = 1 + (z₁ - 1) * ((prmPieceLaw m k).real A) + (z₂ - 1) * ((prmPieceLaw m k).real B) := by
    have hwrw : w = fun x =>
        (1 : ℂ) + A.indicator (fun _ => z₁ - 1) x + B.indicator (fun _ => z₂ - 1) x := by
      funext x
      by_cases hxA : x ∈ A
      · have hxB : x ∉ B := Set.disjoint_left.mp hAB hxA
        simp only [hw_def, Set.indicator_of_mem hxA, Set.indicator_of_notMem hxB,
          ite_eq_left hxA, ite_eq_right hxB]; ring
      · by_cases hxB : x ∈ B
        · simp only [hw_def, Set.indicator_of_notMem hxA, Set.indicator_of_mem hxB,
            ite_eq_right hxA, ite_eq_left hxB]; ring
        · simp only [hw_def, Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxB,
            ite_eq_right hxA, ite_eq_right hxB]; ring
    have hone : ∫ _ : E, (1 : ℂ) ∂(prmPieceLaw m k) = 1 := by simp
    have hfA : Integrable (fun x => (1 : ℂ) + A.indicator (fun _ => z₁ - 1) x) (prmPieceLaw m k) :=
      (integrable_const 1).add ((integrable_const (z₁ - 1)).indicator hA)
    rw [hwrw]
    simp only []
    rw [integral_add hfA ((integrable_const (z₂ - 1)).indicator hB),
      integral_add (integrable_const 1) ((integrable_const (z₁ - 1)).indicator hA),
      hone, integral_indicator_const_complex (z₁ - 1) hA, integral_indicator_const_complex (z₂ - 1) hB]
    ring
  rw [hint]
  have halg : ((m (prmPiece m k)).toReal : ℂ)
        * ((1 + (z₁ - 1) * ((prmPieceLaw m k).real A) + (z₂ - 1) * ((prmPieceLaw m k).real B)) - 1)
      = (((m (prmPiece m k)).toReal * (prmPieceLaw m k).real A : ℝ) : ℂ) * (z₁ - 1)
        + (((m (prmPiece m k)).toReal * (prmPieceLaw m k).real B : ℝ) : ℂ) * (z₂ - 1) := by
    push_cast; ring
  rw [halg, toReal_mul_real_prmPieceLaw hA, toReal_mul_real_prmPieceLaw hB]

/-- The `ℕ → ℝ` cast is a measurable embedding: injective on the countable discrete space `ℕ`. -/
private lemma measurableEmbedding_natCast : MeasurableEmbedding (Nat.cast : ℕ → ℝ) :=
  ⟨Nat.cast_injective, measurable_from_top, fun {t} _ => (t.to_countable.image _).measurableSet⟩

/-- The characteristic function of the `ℝ`-pushforward of the thinned count, from the pgf identity. -/
private lemma charFun_natCast_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (ξ : ℝ) :
    charFun ((μ.map (thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ)) ξ
      = Complex.exp ((m (prmPiece m k ∩ A)).toReal * (Complex.exp (↑ξ * I) - 1)) := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  rw [charFun_apply_real,
    integral_map (φ := (Nat.cast : ℕ → ℝ)) measurable_from_top.aemeasurable (by fun_prop),
    integral_map (φ := thinnedCount K X A k) hTA.aemeasurable (by fun_prop)]
  have hpow : ∀ ω, Complex.exp (↑ξ * ↑((thinnedCount K X A k ω : ℝ)) * I)
      = (Complex.exp (↑ξ * I)) ^ (thinnedCount K X A k ω) := by
    intro ω
    rw [show (↑ξ : ℂ) * ↑((thinnedCount K X A k ω : ℝ)) * I
        = ↑(thinnedCount K X A k ω) * (↑ξ * I) from by push_cast; ring, Complex.exp_nat_mul]
  simp_rw [hpow]
  exact integral_pow_thinnedCount hd hA (Complex.exp (↑ξ * I))
    (le_of_eq (Complex.norm_exp_ofReal_mul_I ξ))

/-- **Poisson thinning within a piece.** The count of piece-`k` points landing in a measurable set
`A` is Poisson-distributed with mean `m (piece k ∩ A)`. Read off the pgf identity by matching the
characteristic function of the `ℝ`-pushforward against `charFun_map_cast_poissonMeasure` and descending
along the injective `ℕ → ℝ` cast. -/
theorem map_thinnedCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) :
    μ.map (thinnedCount K X A k) = poissonMeasure (m (prmPiece m k ∩ A)).toNNReal := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  have hcast : (μ.map (thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ)
      = (poissonMeasure (m (prmPiece m k ∩ A)).toNNReal).map (Nat.cast : ℕ → ℝ) := by
    apply Measure.ext_of_charFun
    funext ξ
    rw [charFun_natCast_thinnedCount hd hA ξ, charFun_map_cast_poissonMeasure,
      ENNReal.coe_toNNReal_eq_toReal]
  exact measurableEmbedding_natCast.map_injective hcast

/-- The characteristic function (via the real dual) of the `ℝ`-pushforward of the thinned count. -/
private lemma charFunDual_natCast_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (M : StrongDual ℝ ℝ) :
    charFunDual ((μ.map (thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ)) M
      = Complex.exp ((m (prmPiece m k ∩ A)).toReal * (Complex.exp (↑(M 1) * I) - 1)) := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  rw [charFunDual_apply,
    integral_map (φ := (Nat.cast : ℕ → ℝ)) measurable_from_top.aemeasurable (by fun_prop),
    integral_map (φ := thinnedCount K X A k) hTA.aemeasurable (by fun_prop)]
  have hpow : ∀ ω, Complex.exp (↑(M ↑(thinnedCount K X A k ω)) * I)
      = (Complex.exp (↑(M 1) * I)) ^ (thinnedCount K X A k ω) := by
    intro ω
    rw [real_dual_apply M ↑(thinnedCount K X A k ω),
      show (↑((thinnedCount K X A k ω : ℝ) * M 1) : ℂ) * I
        = ↑(thinnedCount K X A k ω) * (↑(M 1) * I) from by push_cast; ring, Complex.exp_nat_mul]
  simp_rw [hpow]
  exact integral_pow_thinnedCount hd hA (Complex.exp (↑(M 1) * I))
    (le_of_eq (Complex.norm_exp_ofReal_mul_I (M 1)))

/-- The joint characteristic function (via the dual of `ℝ × ℝ`) of the `ℝ²`-pushforward of the pair
of thinned counts factorizes, by the disjoint two-indicator pgf identity. Exposed (non-`private`) for
the superposition-independence induction in `PoissonRandomMeasure`. -/
lemma charFunDual_prod_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual (μ.map fun ω =>
        ((thinnedCount K X A k ω : ℝ), (thinnedCount K X B k ω : ℝ))) L
      = Complex.exp ((m (prmPiece m k ∩ A)).toReal * (Complex.exp (↑(L.comp (.inl ℝ ℝ ℝ) 1) * I) - 1))
        * Complex.exp ((m (prmPiece m k ∩ B)).toReal *
            (Complex.exp (↑(L.comp (.inr ℝ ℝ ℝ) 1) * I) - 1)) := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  have hTB : Measurable (thinnedCount K X B k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hB
  rw [charFunDual_apply, integral_map
      (φ := fun ω => ((thinnedCount K X A k ω : ℝ), (thinnedCount K X B k ω : ℝ)))
      ((measurable_from_top.comp hTA).prodMk (measurable_from_top.comp hTB)).aemeasurable
      (by fun_prop)]
  have hpow : ∀ ω, Complex.exp
        (↑(L ((thinnedCount K X A k ω : ℝ), (thinnedCount K X B k ω : ℝ))) * I)
      = (Complex.exp (↑(L.comp (.inl ℝ ℝ ℝ) 1) * I)) ^ (thinnedCount K X A k ω)
        * (Complex.exp (↑(L.comp (.inr ℝ ℝ ℝ) 1) * I)) ^ (thinnedCount K X B k ω) := by
    intro ω
    rw [prod_dual_apply L (thinnedCount K X A k ω : ℝ) (thinnedCount K X B k ω : ℝ),
      show (↑((thinnedCount K X A k ω : ℝ) * (L.comp (.inl ℝ ℝ ℝ) 1)
            + (thinnedCount K X B k ω : ℝ) * (L.comp (.inr ℝ ℝ ℝ) 1)) : ℂ) * I
          = ↑(thinnedCount K X A k ω) * (↑(L.comp (.inl ℝ ℝ ℝ) 1) * I)
            + ↑(thinnedCount K X B k ω) * (↑(L.comp (.inr ℝ ℝ ℝ) 1) * I) from by push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul]
  simp_rw [hpow]
  exact integral_pow_thinnedCount_mul hd hA hB hAB _ _
    (le_of_eq (Complex.norm_exp_ofReal_mul_I _)) (le_of_eq (Complex.norm_exp_ofReal_mul_I _))

/-- **Within-piece independence of thinned counts.** Within a single piece `k`, the counts of points
landing in two disjoint measurable sets `A` and `B` are independent. The joint characteristic
function factorizes (the disjoint two-indicator pgf identity), so the `ℝ²`-pushforward of the pair is
a product measure; descending along the injective `ℕ² → ℝ²` cast gives independence. -/
theorem indepFun_thinnedCount_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) :
    IndepFun (thinnedCount K X A k) (thinnedCount K X B k) μ := by
  classical
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  have hTB : Measurable (thinnedCount K X B k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hB
  rw [indepFun_iff_map_prod_eq_prod_map_map hTA.aemeasurable hTB.aemeasurable]
  refine (measurableEmbedding_natCast.prodMap measurableEmbedding_natCast).map_injective ?_
  rw [Measure.map_map (measurableEmbedding_natCast.measurable.prodMap
        measurableEmbedding_natCast.measurable) (hTA.prodMk hTB),
    ← Measure.map_prod_map (μ.map (thinnedCount K X A k)) (μ.map (thinnedCount K X B k))
      measurableEmbedding_natCast.measurable measurableEmbedding_natCast.measurable]
  show μ.map (fun ω => ((thinnedCount K X A k ω : ℝ), (thinnedCount K X B k ω : ℝ)))
      = ((μ.map (thinnedCount K X A k)).map (Nat.cast : ℕ → ℝ)).prod
        ((μ.map (thinnedCount K X B k)).map (Nat.cast : ℕ → ℝ))
  refine (charFunDual_eq_prod_iff).mp fun L => ?_
  rw [charFunDual_prod_thinnedCount hd hA hB hAB L,
    charFunDual_natCast_thinnedCount hd hA (L.comp (.inl ℝ ℝ ℝ)),
    charFunDual_natCast_thinnedCount hd hB (L.comp (.inr ℝ ℝ ℝ))]

/-- A linear form on a finite pi-power of `ℝ` acts by weighted coordinate sums:
`L x = ∑ i, x i · L (Pi.single i 1)`. -/
private lemma pi_dual_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (ι → ℝ)) (x : ι → ℝ) :
    L x = ∑ i, x i * L (Pi.single i 1) := by
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_dual_apply (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) (x i)]
  rfl

open Classical in
omit [MeasurableSpace E] [Nonempty E] in
/-- On a pairwise disjoint family, the product of two-valued `if`s telescopes to a sum: each point
lies in at most one `A i`, so at most one factor differs from `1`. -/
private lemma prod_ite_eq_one_add_sum_indicator {ι : Type} [Fintype ι] {A : ι → Set E}
    (hdisj : Pairwise (Function.onFun Disjoint A)) (z : ι → ℂ) (x : E) :
    ∏ i, (if x ∈ A i then z i else 1)
      = 1 + ∑ i, (A i).indicator (fun _ => z i - 1) x := by
  by_cases hx : ∃ i, x ∈ A i
  · obtain ⟨i₀, hi₀⟩ := hx
    have huniq : ∀ i, i ≠ i₀ → x ∉ A i := fun i hi hmem =>
      Set.disjoint_left.mp (hdisj hi) hmem hi₀
    rw [Finset.prod_eq_single i₀ (fun i _ hi => ite_eq_right (huniq i hi)) (by simp), ite_eq_left hi₀,
      Finset.sum_eq_single i₀ (fun i _ hi => Set.indicator_of_notMem (huniq i hi) _) (by simp),
      Set.indicator_of_mem hi₀]
    ring
  · push Not at hx
    rw [Finset.prod_eq_one (fun i _ => ite_eq_right (hx i)),
      Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (hx i) _)]
    ring

/-- **Joint pgf identity within a piece.** For a pairwise disjoint family of measurable sets, the
joint probability-generating function of the thinned counts factorizes across the pieces:
`E[∏ᵢ zᵢ ^ (thinnedCount (A i))] = ∏ᵢ exp (m (piece k ∩ A i) · (zᵢ − 1))` for `‖zᵢ‖ ≤ 1`. -/
lemma integral_prod_pow_thinnedCount {ι : Type} [Fintype ι] [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∫ ω, ∏ i, (z i) ^ (thinnedCount K X (A i) k ω) ∂μ
      = ∏ i, Complex.exp ((m (prmPiece m k ∩ A i)).toReal * (z i - 1)) := by
  classical
  set w : E → ℂ := fun x => ∏ i, (if x ∈ A i then z i else 1) with hw_def
  have hwmeas : Measurable w :=
    Finset.measurable_prod _ fun i _ => Measurable.ite (hA i) measurable_const measurable_const
  have hwbdd : ∀ x, ‖w x‖ ≤ 1 := by
    intro x
    rw [hw_def, norm_prod]
    refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
    split_ifs with hx
    · exact hz i
    · simp
  have hprod : ∀ ω, ∏ i, (z i) ^ (thinnedCount K X (A i) k ω)
      = ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    simp only [hw_def]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [prod_ite_const (Finset.range (K k ω)) (fun n => X k n ω ∈ A i) (z i), thinnedCount]
  simp_rw [hprod]
  rw [integral_pieceProd_eq_exp hd hwmeas hwbdd]
  have hint : ∫ x, w x ∂(prmPieceLaw m k)
      = 1 + ∑ i, (z i - 1) * ((prmPieceLaw m k).real (A i)) := by
    have hwrw : w = fun x => (1 : ℂ) + ∑ i, (A i).indicator (fun _ => z i - 1) x := by
      funext x; rw [hw_def]; exact prod_ite_eq_one_add_sum_indicator hdisj z x
    have hintegrable : ∀ i,
        Integrable (fun x => (A i).indicator (fun _ => z i - 1) x) (prmPieceLaw m k) :=
      fun i => (integrable_const (z i - 1)).indicator (hA i)
    have hone : ∫ _ : E, (1 : ℂ) ∂(prmPieceLaw m k) = 1 := by simp
    rw [hwrw, integral_add (integrable_const 1) (integrable_finsetSum _ fun i _ => hintegrable i),
      integral_finsetSum _ (fun i _ => hintegrable i), hone]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const_complex (z i - 1) (hA i)]
    ring
  rw [hint,
    show ((m (prmPiece m k)).toReal : ℂ)
          * ((1 + ∑ i, (z i - 1) * ((prmPieceLaw m k).real (A i))) - 1)
        = ∑ i, (((m (prmPiece m k)).toReal * (prmPieceLaw m k).real (A i) : ℝ) : ℂ) * (z i - 1) from ?_]
  · rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toReal_mul_real_prmPieceLaw (hA i)]
  · push_cast
    rw [add_sub_cancel_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The joint characteristic function (via the dual of `ι → ℝ`) of the pushforward of a finite family
of thinned counts factorizes across the pieces, by the joint pgf identity. Public: consumed by the
mutual-independence identification. -/
lemma charFunDual_pi_thinnedCount {ι : Type} [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (thinnedCount K X (A i) k ω : ℝ)) L
      = ∏ i, Complex.exp ((m (prmPiece m k ∩ A i)).toReal
          * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  have hT : ∀ i, Measurable (thinnedCount K X (A i) k) := fun i =>
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) (hA i)
  rw [charFunDual_apply, integral_map
      (φ := fun ω (i : ι) => (thinnedCount K X (A i) k ω : ℝ))
      (Measurable.of_eval fun i => (measurable_from_top.comp (hT i))).aemeasurable (by fun_prop)]
  have hpow : ∀ ω, Complex.exp (↑(L fun i => (thinnedCount K X (A i) k ω : ℝ)) * I)
      = ∏ i, (Complex.exp (↑(L (Pi.single i 1)) * I)) ^ (thinnedCount K X (A i) k ω) := by
    intro ω
    rw [pi_dual_apply L (fun i => (thinnedCount K X (A i) k ω : ℝ)),
      show (↑(∑ i, (thinnedCount K X (A i) k ω : ℝ) * L (Pi.single i 1)) : ℂ) * I
          = ∑ i, ↑(thinnedCount K X (A i) k ω) * (↑(L (Pi.single i 1)) * I) from by
        push_cast; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring,
      Complex.exp_sum]
    exact Finset.prod_congr rfl fun i _ => Complex.exp_nat_mul _ _
  simp_rw [hpow]
  exact integral_prod_pow_thinnedCount hd hA hdisj
    (fun i => Complex.exp (↑(L (Pi.single i 1)) * I))
    (fun i => le_of_eq (Complex.norm_exp_ofReal_mul_I _))

/-- **Mutual independence of thinned counts within a piece.** Within a single piece `k`, the counts
of points landing in a pairwise disjoint finite family of measurable sets `A i` are mutually
independent. The joint characteristic function of the `ℝ`-pushforward factorizes (the joint pgf
identity), so the family is independent as `ℝ`-valued variables; descend along `Nat.floor` to the
`ℕ`-valued counts. -/
theorem iIndepFun_thinnedCount {ι : Type} [Fintype ι] [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i => thinnedCount K X (A i) k) μ := by
  classical
  have hT : ∀ i, Measurable (thinnedCount K X (A i) k) := fun i =>
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) (hA i)
  have hReal : iIndepFun (fun i ω => (thinnedCount K X (A i) k ω : ℝ)) μ := by
    rw [iIndepFun_iff_charFunDual_pi (X := fun i ω => (thinnedCount K X (A i) k ω : ℝ))
      fun i => (measurable_from_top.comp (hT i)).aemeasurable]
    intro L
    rw [charFunDual_pi_thinnedCount hd hA hdisj L]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hmap : (μ.map fun ω => (thinnedCount K X (A i) k ω : ℝ))
        = (μ.map (thinnedCount K X (A i) k)).map (Nat.cast : ℕ → ℝ) := by
      rw [Measure.map_map measurable_from_top (hT i)]; rfl
    rw [hmap, charFunDual_natCast_thinnedCount hd (hA i)
      (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i))]
    rfl
  have hfloor := hReal.comp (fun _ => Nat.floor) (fun _ => Nat.measurable_floor)
  simp only [Function.comp_def, Nat.floor_natCast] at hfloor
  exact hfloor

end Thinning

end ProbabilityTheory
