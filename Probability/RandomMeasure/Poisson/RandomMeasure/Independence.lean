/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Probability.RandomMeasure.Poisson.RandomMeasure.Basic

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Probability.RandomMeasure.Poisson.RandomMeasure.Evaluation
import all Probability.RandomMeasure.Poisson.RandomMeasure.Lemmas

/-!
# Independence of Poisson random-measure evaluations

Counts on disjoint measurable finite-mass regions are independent. The module proves both the
pairwise API and mutual independence for finite pairwise-disjoint families.

For a Poisson point family on a probability space and measurable `A`, `B` with
`Disjoint A B`, `m A < ⊤`, and `m B < ⊤`,
`IndepFun (fun ω => poissonRandomMeasure K X ω A)
  (fun ω => poissonRandomMeasure K X ω B) μ`.
For a finite family `A : ι → Set E` of pairwise-disjoint measurable sets with each `m (A i) < ⊤`,
`iIndepFun (fun i ω => poissonRandomMeasure K X ω (A i)) μ`.

## Public declarations

- `indepFun_poissonRandomMeasure_apply` proves independence of the two counts on disjoint finite-mass
  measurable sets.
- `iIndepFun_poissonRandomMeasure_apply` proves mutual independence for a finite pairwise-disjoint
  family of finite-mass measurable sets.

Write `\mathcal N_\omega(A)=\operatorname{poissonRandomMeasure}(K,X,\omega)(A)`.
For pairwise-disjoint measurable sets of finite intensity, these realized
Poisson counts are mutually independent; in particular, two disjoint regions
give independent counts:

\[\begin{aligned}
\bigl(\omega\mapsto\mathcal N_\omega(A_i)\bigr)_{i\in I}
&\text{ are mutually independent under }\mu,\\
A\cap B=\varnothing&\Longrightarrow
  \bigl(\omega\mapsto\mathcal N_\omega(A)\bigr)
  \ \perp\!\!\!\perp_\mu\ \bigl(\omega\mapsto\mathcal N_\omega(B)\bigr).
\end{aligned}\]
-/

@[expose] public section

open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m]
    [Nonempty E] {μ : Measure Ω} {A B : Set E} {ω : Ω}


/-! ### Marginal characteristic functions

The finite-family result below identifies mutual independence through joint characteristic functions.
For one coordinate, `charFun_toReal_poissonRandomMeasure_apply` derives the ordinary Poisson
characteristic function from the evaluation law; the same identity supplies each marginal in the
finite-dimensional factorization. The two-set independence API is then a Bool-indexed consequence of
the finite-family theorem. -/

/-- A real linear form on `ℝ` acts by scaling: `M r = r · M 1`. -/
private lemma real_dual_apply (M : StrongDual ℝ ℝ) (r : ℝ) : M r = r * M 1 := by
  conv_rhs => rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- On `ℝ`, the characteristic function through a real linear form is the ordinary characteristic
function evaluated at `M 1`. -/
private lemma charFunDual_real_eq_charFun (ν : Measure ℝ) (M : StrongDual ℝ ℝ) :
    charFunDual ν M = charFun ν (M 1) := by
  rw [charFunDual_apply, charFun_apply_real]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Complex.exp (↑(M x) * I) = Complex.exp (↑(M 1) * ↑x * I)
  rw [real_dual_apply M x]
  congr 1
  push_cast
  ring

/-- The real-valued count has the Poisson characteristic function, obtained by applying
`ENNReal.toReal` to the public evaluation law. -/
private lemma charFun_toReal_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) (ξ : ℝ) :
    charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ
      = Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)) := by
  have hN_meas :=
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA
  have hRlaw : μ.map (fun ω => (poissonRandomMeasure K X ω A).toReal)
      = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ) := by
    calc
      μ.map (fun ω => (poissonRandomMeasure K X ω A).toReal)
          = (μ.map fun ω => poissonRandomMeasure K X ω A).map ENNReal.toReal := by
              rw [show (fun ω => (poissonRandomMeasure K X ω A).toReal)
                    = ENNReal.toReal ∘ fun ω => poissonRandomMeasure K X ω A from rfl,
                ← Measure.map_map ENNReal.measurable_toReal hN_meas]
      _ = ((poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)).map ENNReal.toReal :=
        congrArg (fun ν : Measure ℝ≥0∞ => ν.map ENNReal.toReal)
          (map_poissonRandomMeasure_apply hd hA hfin)
      _ = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ) := by
        rw [Measure.map_map ENNReal.measurable_toReal measurable_from_top]
        congr 1
  rw [hRlaw, charFun_map_cast_poissonMeasure, ENNReal.coe_toNNReal_eq_toReal]

/-! ### Mutual independence of the counts in a finite disjoint family

For a finite pairwise-disjoint family `A : ι → Set E`, the joint characteristic function of the
partial-count vector factorizes across coordinates by induction on the number of pieces, using the
point-family joint pgf `charFunDual_pi_thinnedCount`. Dominated convergence passes this factorization
to the total counts, and Mathlib's `iIndepFun_iff_charFunDual_pi` identifies mutual independence. -/

/-- **Prefix-versus-next-piece independence of the superposition-count vector.** The family of partial
counts from the first `n + 1` pieces is independent of the family of thinned counts of piece `n + 1`.
The two disjoint coordinate families are selected through the public point-family split theorem. -/
private lemma indepFun_prmPartialCountVec_thinnedCountVec {ι : Type} [Fintype ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    IndepFun (fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ))
      (fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℝ)) μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ)) (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1)) (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;> simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;> simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
      ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := hd.indepFun_pointFamily_split φ ψ hφ_inj hψ_inj hST
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType E (φ i)) → (ι → ℕ) :=
    fun g (i : ι) => ∑ k : Fin (n + 1),
      ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ A i).card with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType E (ψ j)) → (ι → ℕ) :=
    fun g (i : ι) =>
      ((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ A i).card with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact Measurable.of_eval fun i => Finset.measurable_sum _ fun k _ =>
      measurable_filterCard (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        (hA i) (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H := by
    rw [hH_def]
    exact Measurable.of_eval fun i =>
      measurable_filterCard (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
        (hA i) (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω)
      = fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℕ) := by
    funext ω i
    simp only [hG_def]
    unfold prmPartialCount
    rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X (A i) j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω)
      = fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℕ) := by
    funext ω i; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rw [hGeq, hHeq] at key
  have hcast := key.comp (φ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (ψ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (Measurable.of_eval fun i => measurable_from_top.comp (measurable_pi_apply i))
    (Measurable.of_eval fun i => measurable_from_top.comp (measurable_pi_apply i))
  simpa only [Function.comp_def] using hcast

/-- **Joint characteristic function of the partial superposition-count vector.** It factorizes across
the family into the Poisson pgfs with the accumulated `A i`-rates, by induction on the number of
pieces: the base case is the within-piece factorization `charFunDual_pi_thinnedCount`, and each
step adds an independent block. -/
private lemma charFunDual_prmPartialCountVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A)) (n : ℕ)
    (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ)) L
      = ∏ i, Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A i)).toReal)
          * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  induction n with
  | zero =>
    have h0 : (fun ω (i : ι) => (prmPartialCount K X (A i) 0 ω : ℝ))
        = fun ω (i : ι) => (thinnedCount K X (A i) 0 ω : ℝ) := by
      funext ω i; rw [prmPartialCount, Finset.sum_range_one]
    rw [h0, charFunDual_pi_thinnedCount hd hA hdisj L]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  | succ n ih =>
    have mPn : Measurable fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ) :=
      Measurable.of_eval fun i => measurable_from_top.comp
        (measurable_prmPartialCount hd.measurable_count hd.measurable_point (hA i) n)
    have mQn : Measurable fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℝ) :=
      Measurable.of_eval fun i => measurable_from_top.comp
        (measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) (hA i))
    have hsucc : (fun ω (i : ι) => (prmPartialCount K X (A i) (n + 1) ω : ℝ))
        = fun ω => (fun i => (prmPartialCount K X (A i) n ω : ℝ))
            + fun i => (thinnedCount K X (A i) (n + 1) ω : ℝ) := by
      funext ω i
      simp only [Pi.add_apply]
      rw [prmPartialCount, Finset.sum_range_succ, Nat.cast_add]; rfl
    rw [hsucc, IndepFun.charFunDual_map_fun_add_eq_mul mPn.aemeasurable mQn.aemeasurable
        (indepFun_prmPartialCountVec_thinnedCountVec hd hA n), Pi.mul_apply, ih,
      charFunDual_pi_thinnedCount hd hA hdisj L, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ A i)).toReal) (n + 1), ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- **Joint characteristic function of the count vector.** By dominated convergence from the partial
counts: the count vectors converge almost surely on the (finite) intersection of the coordinatewise
finiteness events, the integrands are bounded by `1`, and the accumulated rates increase to `m (A i)`
per coordinate. -/
private lemma charFunDual_poissonRandomMeasureVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal) L
      = ∏ i, Complex.exp (↑(m (A i)).toReal * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  have mPn : ∀ n, Measurable fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ) := fun n =>
    Measurable.of_eval fun i => measurable_from_top.comp
      (measurable_prmPartialCount hd.measurable_count hd.measurable_point (hA i) n)
  have mN : Measurable fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal :=
    Measurable.of_eval fun i =>
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
        (hA i)).ennreal_toReal
  have hFmeas : ∀ n, Measurable fun ω =>
      Complex.exp (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I) := fun n =>
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (L.continuous.measurable.comp (mPn n))).mul_const I)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp
      (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := by
    intro n; filter_upwards with ω
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hae : ∀ᵐ ω ∂μ, ∀ i, poissonRandomMeasure K X ω (A i) < ⊤ := by
    rw [ae_all_iff]
    exact fun i => ae_poissonRandomMeasure_apply_lt_top hd (hA i) (hfin i)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Complex.exp
      (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I)) atTop
      (𝓝 (Complex.exp (↑(L fun i => (poissonRandomMeasure K X ω (A i)).toReal) * I))) := by
    filter_upwards [hae] with ω hω
    have hc : Continuous fun p : ι → ℝ => Complex.exp (↑(L p) * I) := by fun_prop
    exact (hc.tendsto _).comp
      (tendsto_pi_nhds.mpr fun i => tendsto_natCast_prmPartialCount (hA i) ω (hω i))
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1 : ℝ)) (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have key : ∀ n, ∫ ω, Complex.exp
        (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I) ∂μ
      = charFunDual (μ.map fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ)) L := fun n => by
    rw [charFunDual_apply, integral_map (mPn n).aemeasurable (by fun_prop)]
  have keyN : ∫ ω, Complex.exp
        (↑(L fun i => (poissonRandomMeasure K X ω (A i)).toReal) * I) ∂μ
      = charFunDual (μ.map fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal) L := by
    rw [charFunDual_apply, integral_map mN.aemeasurable (by fun_prop)]
  simp_rw [key, charFunDual_prmPartialCountVec hd hA hdisj] at hdct
  rw [keyN] at hdct
  have hrate : Tendsto (fun n => ∏ i,
      Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A i)).toReal)
        * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1))) atTop
      (𝓝 (∏ i, Complex.exp (↑(m (A i)).toReal * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)))) := by
    refine tendsto_finsetProd _ fun i _ => ?_
    exact ((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
        Complex.exp (↑r * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount (hA i) (hfin i))
  exact tendsto_nhds_unique hdct hrate

/-- The `ℝ`-valued counts in a finite pairwise disjoint family of finite-mass sets are mutually
independent: their joint characteristic function is the product of the marginals, using the Poisson
evaluation law for each marginal. -/
private lemma iIndepFun_natCast_poissonRandomMeasure_apply {ι : Type} [Fintype ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω => (poissonRandomMeasure K X ω (A i)).toReal) μ := by
  classical
  rw [iIndepFun_iff_charFunDual_pi
    (X := fun i ω => (poissonRandomMeasure K X ω (A i)).toReal)
    fun i => (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
      (hA i)).ennreal_toReal.aemeasurable]
  intro L
  rw [charFunDual_poissonRandomMeasureVec hd hA hfin hdisj L]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [charFunDual_real_eq_charFun, charFun_toReal_poissonRandomMeasure_apply hd (hA i) (hfin i)]
  rfl

/-- **Mutual independence of the counts in a finite disjoint family.** For a pairwise disjoint finite
family `A i` of finite-mass measurable sets, the counts `poissonRandomMeasure K X · (A i)` are mutually
independent. The `ℝ`-valued counts are mutually independent
(`iIndepFun_natCast_poissonRandomMeasure_apply`), and this is transported to the `ℝ≥0∞`-valued counts
through `ENNReal.ofReal` using the almost-sure finiteness. -/
theorem iIndepFun_poissonRandomMeasure_apply {ι : Type} [Fintype ι] [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω => poissonRandomMeasure K X ω (A i)) μ := by
  have hcomp := (iIndepFun_natCast_poissonRandomMeasure_apply hd hA hfin hdisj).comp
    (fun _ => ENNReal.ofReal) (fun _ => ENNReal.continuous_ofReal.measurable)
  refine (iIndepFun_congr fun i => ?_).mp hcomp
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd (hA i) (hfin i)] with ω hω
  rw [Function.comp_apply, ENNReal.ofReal_toReal hω.ne]


/-- **Pairwise independence of the counts in disjoint sets.** For two disjoint finite-mass measurable
sets `A` and `B`, the counts `poissonRandomMeasure K X · A` and `poissonRandomMeasure K X · B` are
independent. This is the two-coordinate specialization of
`iIndepFun_poissonRandomMeasure_apply`. -/
theorem indepFun_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤) (hAB : Disjoint A B) :
    IndepFun (fun ω => poissonRandomMeasure K X ω A) (fun ω => poissonRandomMeasure K X ω B) μ := by
  let sets : Bool → Set E := fun b => if b then B else A
  have hsets : ∀ i, MeasurableSet (sets i) := by
    intro i
    cases i with
    | false => exact hA
    | true => exact hB
  have hfinite : ∀ i, m (sets i) < ⊤ := by
    intro i
    cases i with
    | false => exact hfinA
    | true => exact hfinB
  have hdisj : Pairwise (Function.onFun Disjoint sets) := by
    intro i j hij
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · simpa [Function.onFun, sets] using hAB
    · simpa [Function.onFun, sets] using hAB.symm
    · exact False.elim (hij rfl)
  have hmutual := iIndepFun_poissonRandomMeasure_apply (A := sets) hd hsets hfinite hdisj
  have hpair := hmutual.indepFun (i := false) (j := true) (by decide)
  simpa [sets] using hpair


end ProbabilityTheory
