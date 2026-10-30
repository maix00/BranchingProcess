/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Probability.RandomMeasure.Poisson.PointFamily.Independence

import Probability.Distributions.Poisson.Moments
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Integration

/-!
# Poisson point-family sums and moment identities

For a measurable test function, this module studies the finite sum of its values over the marks
in one partition piece. It proves Campbell's formula, the second-moment identity, and independence
between sums over distinct pieces and between consecutive blocks.

## Public declarations

- `pieceSum` is $\sum_{n<K_k(ω)} f(X_{k,n}(ω))$;
  `measurable_pieceSum` gives measurability under measurable counts, marks, and integrand.
- `integral_pieceSum` is Campbell's formula when $[\mathrm{IsProbabilityMeasure}(\mu)]$,
  the point-family law is $\mu$, and $f$ is measurable and integrable on the piece:
  $\mathbb E[\operatorname{pieceSum}(f,k)] = \int_{\operatorname{prmPiece}(m,k)} f\,dm$.
- `integrable_sq_pieceSum` proves square integrability under piecewise integrability of $f$ and
  $f^2$. `integral_sq_pieceSum` gives
  $\mathbb E[\operatorname{pieceSum}(f,k)^2]
    =\int_{\operatorname{prmPiece}(m,k)}f^2\,dm
      +\left(\int_{\operatorname{prmPiece}(m,k)}f\,dm\right)^2$.
- `indepFun_pieceSum_pieceSum` proves independence for sums over distinct pieces, and
  `indepFun_pieceSum_prefix_next` proves independence of the sum over pieces $0,\ldots,n$ from
  the sum over piece $n+1$.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-! ### Piece sums, Campbell's formula, and the second-moment identity

For a fixed piece `k` and a test function `f`, the *piece sum* `pieceSum K X f k ω` is the sum of `f`
over the `K k ω` points of that piece. Campbell's formula computes its mean as the `m`-integral of
`f` over the piece; the second-moment identity computes `E[(pieceSum)²]` as
`∫ f² dm + (∫ f dm)²` over the piece. Both are proved by conditioning on the piece count `K k`: on
`{K k = j}` the piece sum is a fixed sum of `j` i.i.d. marks, and the count is independent of the
marks, so each conditional expectation factors; summing over `j` against the Poisson mean and second
factorial moment gives the result. -/

section PieceSum

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ}

/-- The **piece sum**: the sum of the test function `f` over the `K k ω` points of piece `k`. -/
noncomputable def pieceSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (f : E → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range (K k ω), f (X k n ω)

omit [Nonempty E] in
/-- The piece sum is measurable, since it is a countable-index composition of the measurable count
and the measurable points. -/
theorem measurable_pieceSum {f : E → ℝ} (hK : Measurable (K k))
    (hX : ∀ n, Measurable (X k n))
    (hf : Measurable f) : Measurable (pieceSum K X f k) := by
  have hP : Measurable (fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, f (X k n p.1)) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ => hf.comp (hX n)
  exact hP.comp (measurable_id.prodMk hK)

/-- A test function integrable on a piece is integrable against that piece's normalized law: on a
positive-mass piece the law is a finite rescaling of the restriction, and on a zero-mass piece it is
a Dirac mass. -/
private lemma integrable_prmPieceLaw {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) : Integrable g (prmPieceLaw m k) := by
  unfold prmPieceLaw
  split_ifs with h
  · exact integrable_dirac' hg.stronglyMeasurable (by finiteness)
  · exact (integrable_smul_measure (ENNReal.inv_ne_zero.2 (measure_prmPiece_lt_top).ne)
      (ENNReal.inv_ne_top.2 h)).mpr hgi

/-- Unconditional scaling bridge: the `m`-mass of the piece times the Bochner integral against the
normalized law is the set integral against `m`, including the zero-mass piece where both sides
vanish. -/
private lemma toReal_mul_integral_prmPieceLaw (g : E → ℝ) :
    (m (prmPiece m k)).toReal * ∫ x, g x ∂(prmPieceLaw m k) = ∫ x in prmPiece m k, g x ∂m := by
  by_cases h : m (prmPiece m k) = 0
  · rw [h, ENNReal.toReal_zero, zero_mul,
      show (∫ x in prmPiece m k, g x ∂m) = ∫ x, g x ∂(m.restrict (prmPiece m k)) from rfl,
      Measure.restrict_eq_zero.mpr h, integral_zero_measure]
  · rw [← integral_smul_prmPieceLaw h, smul_eq_mul]

/-- Each mark `X k n` integrates `g` to the piece-law integral, and the sum of the first `j` marks
therefore integrates to `j` times that value. -/
private lemma integral_marksSum_eq [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {g : E → ℝ} (hg : Measurable g) (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ = (j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k) := by
  have hterm : ∀ n, Integrable (fun ω => g (X k n ω)) μ := by
    intro n
    have hI : Integrable g (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hg hgi
    exact hI.comp_measurable (hd.measurable_point k n)
  have heach : ∀ n, ∫ ω, g (X k n ω) ∂μ = ∫ x, g x ∂(prmPieceLaw m k) := by
    intro n
    rw [← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hg.aestronglyMeasurable]
  rw [integral_finsetSum _ (fun n _ => hterm n)]
  simp_rw [heach]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Conditional Campbell factorization.** On the event `{K k = j}` the integral of the sum of the
first `j` marks factors as the probability of the event times `j` times the piece-law integral, by
independence of the count from the marks. -/
private lemma setIntegral_count_rangeSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {g : E → ℝ} (hg : Measurable g)
    (hgi : Integrable g (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω in {ω | K k ω = j}, ∑ n ∈ Finset.range j, g (X k n ω) ∂μ
      = μ.real {ω | K k ω = j} * ((j : ℝ) * ∫ x, g x ∂(prmPieceLaw m k)) := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  set Xk : Ω → (ℕ → E) := fun ω n => X k n ω with hXk
  have hXk_meas : Measurable Xk := Measurable.of_eval fun n => hd.measurable_point k n
  set ψ : (ℕ → E) → ℝ := fun y => ∑ n ∈ Finset.range j, g (y n) with hψ
  have hψ_meas : Measurable ψ :=
    Finset.measurable_sum _ fun n _ => hg.comp (measurable_pi_apply n)
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (Xk ω))
      = fun ω => (if K k ω = j then (1 : ℝ) else 0) * ψ (Xk ω) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr,
    (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0) (g := ψ)
      (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ_meas.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℝ) else 0) ∂μ = μ.real {ω | K k ω = j} := by
    have hrw : (fun ω => if K k ω = j then (1 : ℝ) else 0)
        = ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω; by_cases h : K k ω = j <;> simp [Set.mem_ofPred_eq, h]
    rw [hrw, integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  rw [hfirst]
  congr 1
  exact integral_marksSum_eq hd hg hgi j

/-- **Campbell's formula for a piece sum.** The mean of the piece sum is the `m`-integral of the test
function over the piece:
`E[∑_{n < K k} f(X k n)] = ∫_{piece k} f dm`. The zero-mass piece is handled inside: the count is
`0` almost surely and both sides vanish. -/
theorem integral_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ}
    (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k))) :
    ∫ ω, pieceSum K X f k ω ∂μ = ∫ x in prmPiece m k, f x ∂m := by
  classical
  have habs : Measurable fun x => |f x| := continuous_abs.measurable.comp hf
  set rate := (m (prmPiece m k)).toNNReal with hrate
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_ofPred_eq]
    intro ω h1 h2; exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  -- On each cell the piece sum is the fixed sum of the first `j` marks.
  have heqcell : ∀ j, Set.EqOn (pieceSum K X f k)
      (fun ω => ∑ n ∈ Finset.range j, f (X k n ω)) (s j) := by
    intro j ω hω
    show pieceSum K X f k ω = _
    rw [pieceSum, show K k ω = j from hω]
  have hGint : ∀ (g : E → ℝ), Measurable g → Integrable g (m.restrict (prmPiece m k)) → ∀ j,
      Integrable (fun ω => ∑ n ∈ Finset.range j, g (X k n ω)) μ := by
    intro g hg hgi j
    refine integrable_finsetSum _ fun n _ => ?_
    have hI : Integrable g (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hg hgi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hi : ∀ j, IntegrableOn (pieceSum K X f k) (s j) μ := fun j =>
    ((hGint f hf hfi j).integrableOn).congr_fun (heqcell j).symm (hs_meas j)
  -- Bound the per-cell norm integrals by the `|f|`-Campbell terms, which are summable.
  have hbound : ∀ j, ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ
      ≤ (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, |f x| ∂(prmPieceLaw m k)) := by
    intro j
    have hcount : μ.real {ω | K k ω = j} = (poissonMeasure rate).real {j} := by
      exact (hd.law_count k).measureReal_eq (p := fun n => n = j)
        (measurableSet_singleton j)
    have hmono : ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ
        ≤ ∫ x in s j, ∑ n ∈ Finset.range j, |f (X k n x)| ∂μ := by
      refine setIntegral_mono_on ((hi j).norm)
        ((hGint (fun x => |f x|) habs hfi.abs j).integrableOn) (hs_meas j) fun ω hω => ?_
      rw [Real.norm_eq_abs, show pieceSum K X f k ω = ∑ n ∈ Finset.range j, f (X k n ω) from
        heqcell j hω]
      exact Finset.abs_sum_le_sum_abs _ _
    calc ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ
        ≤ ∫ x in s j, ∑ n ∈ Finset.range j, |f (X k n x)| ∂μ := hmono
      _ = (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, |f x| ∂(prmPieceLaw m k)) := by
          rw [setIntegral_count_rangeSum hd habs hfi.abs j, hcount]
  have hsummable : Summable fun j => ∫ x in s j, ‖pieceSum K X f k x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _) hbound ?_
    have hexp : Summable fun (j : ℕ) => (∫ x, |f x| ∂(prmPieceLaw m k)) * ((j : ℝ) * (poissonMeasure rate).real {j}) :=
      ((poissonExpectation_hasSum rate).summable).mul_left _
    refine hexp.congr fun j => ?_
    ring
  have hInt : Integrable (pieceSum K X f k) μ := by
    have h := integrableOn_iUnion_of_summable_integral_norm hi hsummable
    rwa [hunion, integrableOn_univ] at h
  -- Assemble via the countable partition of `Ω`.
  have hval := integral_iUnion hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  have hcellf : ∀ j, ∫ x in s j, pieceSum K X f k x ∂μ
      = (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, f x ∂(prmPieceLaw m k)) := by
    intro j
    have hcount : μ.real {ω | K k ω = j} = (poissonMeasure rate).real {j} := by
      exact (hd.law_count k).measureReal_eq (p := fun n => n = j)
        (measurableSet_singleton j)
    rw [setIntegral_congr_fun (hs_meas j) (heqcell j),
      setIntegral_count_rangeSum hd hf hfi j, hcount]
  simp_rw [hcellf]
  have hfun : (fun j => (poissonMeasure rate).real {j} * ((j : ℝ) * ∫ x, f x ∂(prmPieceLaw m k)))
      = fun (j : ℕ) => (∫ x, f x ∂(prmPieceLaw m k)) * ((j : ℝ) * (poissonMeasure rate).real {j}) := by
    funext j; ring
  have hr : (rate : ℝ) = (m (prmPiece m k)).toReal := rfl
  rw [hfun, ((poissonExpectation_hasSum rate).mul_left (∫ x, f x ∂(prmPieceLaw m k))).tsum_eq, hr,
    mul_comm, toReal_mul_integral_prmPieceLaw (k := k) f]


/-- **General conditional factorization.** On `{K k = j}`, the integral of any measurable functional
of the marks of piece `k` factors as the probability of the event times the functional's integral,
by independence of the count from the marks. -/
private lemma setIntegral_count_marksFun [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (j : ℕ) {ψ : (ℕ → E) → ℝ} (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ
      = μ.real {ω | K k ω = j} * ∫ ω, ψ (fun n => X k n ω) ∂μ := by
  have hmeas : MeasurableSet {ω | K k ω = j} :=
    hd.measurable_count k (measurableSet_singleton j)
  set Xk : Ω → (ℕ → E) := fun ω n => X k n ω with hXk
  have hXk_meas : Measurable Xk := Measurable.of_eval fun n => hd.measurable_point k n
  have hcongr : ({ω | K k ω = j}).indicator (fun ω => ψ (Xk ω))
      = fun ω => (if K k ω = j then (1 : ℝ) else 0) * ψ (Xk ω) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases h : K k ω = j <;> simp [h]
  rw [← integral_indicator hmeas, hcongr,
    (hd.indepFun_count_marks k).integral_fun_comp_mul_comp
      (f := fun c : ℕ => if c = j then (1 : ℝ) else 0) (g := ψ)
      (hd.measurable_count k).aemeasurable hXk_meas.aemeasurable
      (measurable_of_countable _).aestronglyMeasurable hψ.aestronglyMeasurable]
  have hfirst : ∫ ω, (if K k ω = j then (1 : ℝ) else 0) ∂μ = μ.real {ω | K k ω = j} := by
    have hrw : (fun ω => if K k ω = j then (1 : ℝ) else 0)
        = ({ω | K k ω = j}).indicator (fun _ => 1) := by
      funext ω; by_cases h : K k ω = j <;> simp [Set.mem_ofPred_eq, h]
    rw [hrw, integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  rw [hfirst]

/-- The square of the sum of the first `j` marks is integrable: expanding the square gives a finite
sum of products of marks, each integrable (a squared mark on the diagonal, a product of independent
marks off it). -/
private lemma integrable_marksSum_sq [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) (j : ℕ) :
    Integrable (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) μ := by
  classical
  have hInt_f : ∀ n, Integrable (fun ω => f (X k n ω)) μ := by
    intro n
    have hI : Integrable f (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hf hfi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hInt_f2 : ∀ n, Integrable (fun ω => f (X k n ω) ^ 2) μ := by
    intro n
    have hI : Integrable (fun x => f x ^ 2) (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw (hf.pow_const 2) hfi2
    exact hI.comp_measurable (hd.measurable_point k n)
  have hprod : ∀ n n', Integrable (fun ω => f (X k n ω) * f (X k n' ω)) μ := by
    intro n n'
    by_cases h : n = n'
    · subst h; simpa [pow_two] using hInt_f2 n
    · exact (((hd.iIndepFun_point_piece k).indepFun h).comp hf hf).integrable_mul
        (hInt_f n) (hInt_f n')
  have hexp : (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2)
      = fun ω => ∑ n ∈ Finset.range j, ∑ n' ∈ Finset.range j, f (X k n ω) * f (X k n' ω) := by
    funext ω; rw [pow_two, Finset.sum_mul_sum]
  rw [hexp]
  exact integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ => hprod n n'

/-- **Second moment of a fixed-length mark sum.** The mean square of the sum of the first `j` i.i.d.
marks is `j * E[f^2] + j (j-1) * E[f]^2`, against the piece law. Expanding the square, diagonal terms
give `E[f^2]` and off-diagonal terms factor as `E[f]^2` by independence. -/
private lemma integral_marksSum_sq_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ} (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ ω, (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2 ∂μ
      = (j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
        + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2 := by
  classical
  set A := ∫ x, f x ^ 2 ∂(prmPieceLaw m k) with hA
  set B := ∫ x, f x ∂(prmPieceLaw m k) with hB
  have hf2m : Measurable (fun x => f x ^ 2) := hf.pow_const 2
  have hInt_f : ∀ n, Integrable (fun ω => f (X k n ω)) μ := by
    intro n
    have hI : Integrable f (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hf hfi
    exact hI.comp_measurable (hd.measurable_point k n)
  have hInt_f2 : ∀ n, Integrable (fun ω => f (X k n ω) ^ 2) μ := by
    intro n
    have hI : Integrable (fun x => f x ^ 2) (μ.map (X k n)) := by
      rw [(hd.law_point k n).map_eq]; exact integrable_prmPieceLaw hf2m hfi2
    exact hI.comp_measurable (hd.measurable_point k n)
  have heach_f : ∀ n, ∫ ω, f (X k n ω) ∂μ = B := by
    intro n
    rw [hB, ← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hf.aestronglyMeasurable]
  have heach_f2 : ∀ n, ∫ ω, f (X k n ω) ^ 2 ∂μ = A := by
    intro n
    rw [hA, ← (hd.law_point k n).map_eq,
      integral_map (hd.measurable_point k n).aemeasurable hf2m.aestronglyMeasurable]
  have hindep : ∀ n n', n ≠ n' →
      IndepFun (fun ω => f (X k n ω)) (fun ω => f (X k n' ω)) μ :=
    fun n n' h => ((hd.iIndepFun_point_piece k).indepFun h).comp hf hf
  have hprod : ∀ n n', Integrable (fun ω => f (X k n ω) * f (X k n' ω)) μ := by
    intro n n'
    by_cases h : n = n'
    · subst h; simpa [pow_two] using hInt_f2 n
    · exact (hindep n n' h).integrable_mul (hInt_f n) (hInt_f n')
  have hprod_val : ∀ n n', ∫ ω, f (X k n ω) * f (X k n' ω) ∂μ
      = if n = n' then A else B ^ 2 := by
    intro n n'
    by_cases h : n = n'
    · subst h; rw [ite_eq_left rfl]; simp_rw [← pow_two]; exact heach_f2 n
    · rw [ite_eq_right h, (hindep n n' h).integral_fun_mul_eq_mul_integral
        (hInt_f n).aestronglyMeasurable (hInt_f n').aestronglyMeasurable, heach_f n, heach_f n',
        ← pow_two]
  have hexp : (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2)
      = fun ω => ∑ n ∈ Finset.range j, ∑ n' ∈ Finset.range j, f (X k n ω) * f (X k n' ω) := by
    funext ω; rw [pow_two, Finset.sum_mul_sum]
  rw [hexp, integral_finsetSum _ fun n _ =>
    integrable_finsetSum _ fun n' _ => hprod n n']
  have hinner : ∀ n, ∫ ω, ∑ n' ∈ Finset.range j, f (X k n ω) * f (X k n' ω) ∂μ
      = ∑ n' ∈ Finset.range j, (if n = n' then A else B ^ 2) := by
    intro n
    rw [integral_finsetSum _ fun n' _ => hprod n n']
    exact Finset.sum_congr rfl fun n' _ => hprod_val n n'
  simp_rw [hinner]
  have hin : ∀ n ∈ Finset.range j,
      (∑ n' ∈ Finset.range j, (if n = n' then A else B ^ 2)) = A + ((j : ℝ) - 1) * B ^ 2 := by
    intro n hn
    have hrw : ∀ n', (if n = n' then A else B ^ 2)
        = B ^ 2 + (if n = n' then (A - B ^ 2) else 0) := by
      intro n'; split_ifs <;> ring
    simp_rw [hrw]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Finset.sum_ite_eq (Finset.range j) n (fun _ => A - B ^ 2), ite_eq_left hn]
    ring
  rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Per-cell second moment: on `{K k = j}` the mean square of the piece sum is the Poisson pmf at `j`
times the fixed-length second moment `j * E[f^2] + j (j-1) * E[f]^2`. -/
private lemma setIntegral_sq_pieceSum_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {f : E → ℝ} (hf : Measurable f)
    (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) (j : ℕ) :
    ∫ x in {ω | K k ω = j}, (pieceSum K X f k x) ^ 2 ∂μ
      = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j}
        * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
          + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
  have hψmeas : Measurable (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2) :=
    (Finset.measurable_sum _ fun n _ => hf.comp (measurable_pi_apply n)).pow_const 2
  have hcount : μ.real {ω | K k ω = j}
      = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j} := by
    exact (hd.law_count k).measureReal_eq (p := fun n => n = j)
      (measurableSet_singleton j)
  calc ∫ x in {ω | K k ω = j}, (pieceSum K X f k x) ^ 2 ∂μ
      = ∫ x in {ω | K k ω = j},
          (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2) (fun n => X k n x) ∂μ := by
        refine setIntegral_congr_fun (hd.measurable_count k (measurableSet_singleton j)) ?_
        intro ω hω; show (pieceSum K X f k ω) ^ 2 = _
        rw [pieceSum, show K k ω = j from hω]
    _ = μ.real {ω | K k ω = j}
          * ∫ x, (fun y : ℕ → E => (∑ n ∈ Finset.range j, f (y n)) ^ 2) (fun n => X k n x) ∂μ :=
        setIntegral_count_marksFun hd j hψmeas
    _ = (poissonMeasure (m (prmPiece m k)).toNNReal).real {j}
          * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
            + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
        rw [hcount]
        congr 1
        exact integral_marksSum_sq_eq hd hf hfi hfi2 j

/-- The square of a piece sum is integrable: its cell integrals are dominated by the Poisson first
and second factorial moments of the count, which are summable. -/
theorem integrable_sq_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) :
    Integrable (fun ω => (pieceSum K X f k ω) ^ 2) μ := by
  classical
  set rate := (m (prmPiece m k)).toNNReal with hrate
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have heqcell : ∀ j, Set.EqOn (fun ω => (pieceSum K X f k ω) ^ 2)
      (fun ω => (∑ n ∈ Finset.range j, f (X k n ω)) ^ 2) (s j) := by
    intro j ω hω; show (pieceSum K X f k ω) ^ 2 = _; rw [pieceSum, show K k ω = j from hω]
  have hi : ∀ j, IntegrableOn (fun ω => (pieceSum K X f k ω) ^ 2) (s j) μ := fun j =>
    ((integrable_marksSum_sq hd hf hfi hfi2 j).integrableOn).congr_fun (heqcell j).symm (hs_meas j)
  have hsummable : Summable fun j => ∫ x in s j, ‖(pieceSum K X f k x) ^ 2‖ ∂μ := by
    have heqnorm : (fun j => ∫ x in s j, ‖(pieceSum K X f k x) ^ 2‖ ∂μ)
        = fun j => (poissonMeasure rate).real {j}
          * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
            + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) := by
      funext j
      rw [← setIntegral_sq_pieceSum_eq hd hf hfi hfi2 j]
      exact setIntegral_congr_fun (hs_meas j) fun ω _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [heqnorm]
    have h1 : Summable fun (j : ℕ) =>
        (∫ x, f x ^ 2 ∂(prmPieceLaw m k)) * ((j : ℝ) * (poissonMeasure rate).real {j}) :=
      ((poissonExpectation_hasSum rate).summable).mul_left _
    have h2 : Summable fun (j : ℕ) => (∫ x, f x ∂(prmPieceLaw m k)) ^ 2
        * (((j : ℝ) * ((j : ℝ) - 1)) * (poissonMeasure rate).real {j}) :=
      ((poissonFactorialMoment2_hasSum rate).summable).mul_left _
    exact (h1.add h2).congr fun j => by ring
  have h := integrableOn_iUnion_of_summable_integral_norm hi hsummable
  rwa [hunion, integrableOn_univ] at h

/-- **Second-moment identity for a piece sum.** The mean square of the piece sum is
`∫_{piece k} f^2 dm + (∫_{piece k} f dm)^2`; the zero-mass piece is handled inside. -/
theorem integral_sq_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f) (hfi : Integrable f (m.restrict (prmPiece m k)))
    (hfi2 : Integrable (fun x => f x ^ 2) (m.restrict (prmPiece m k))) :
    ∫ ω, (pieceSum K X f k ω) ^ 2 ∂μ
      = (∫ x in prmPiece m k, f x ^ 2 ∂m) + (∫ x in prmPiece m k, f x ∂m) ^ 2 := by
  classical
  set rate := (m (prmPiece m k)).toNNReal with hrate
  set s : ℕ → Set Ω := fun j => {ω | K k ω = j} with hs
  have hs_meas : ∀ j, MeasurableSet (s j) := fun j =>
    hd.measurable_count k (measurableSet_singleton j)
  have hs_disj : Pairwise fun i j => Disjoint (s i) (s j) := by
    intro a b hab
    simp only [Set.disjoint_left, hs, Set.mem_ofPred_eq]
    intro ω h1 h2; exact hab (h1 ▸ h2)
  have hunion : (⋃ j, s j) = Set.univ :=
    Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨K k ω, rfl⟩
  have hInt := integrable_sq_pieceSum hd hf hfi hfi2
  have hval := integral_iUnion hs_meas hs_disj (by rw [hunion]; exact hInt.integrableOn)
  rw [hunion, setIntegral_univ] at hval
  rw [hval]
  have hcell : ∀ j, ∫ x in s j, (pieceSum K X f k x) ^ 2 ∂μ
      = (poissonMeasure rate).real {j}
        * ((j : ℝ) * (∫ x, f x ^ 2 ∂(prmPieceLaw m k))
          + (j : ℝ) * ((j : ℝ) - 1) * (∫ x, f x ∂(prmPieceLaw m k)) ^ 2) :=
    fun j => setIntegral_sq_pieceSum_eq hd hf hfi hfi2 j
  simp_rw [hcell]
  set A := ∫ x, f x ^ 2 ∂(prmPieceLaw m k) with hA
  set B := ∫ x, f x ∂(prmPieceLaw m k) with hB
  have hHS : HasSum
      (fun j => (poissonMeasure rate).real {j} * ((j : ℝ) * A + (j : ℝ) * ((j : ℝ) - 1) * B ^ 2))
      (A * (rate : ℝ) + B ^ 2 * (rate : ℝ) ^ 2) := by
    have h1 := (poissonExpectation_hasSum rate).mul_left A
    have h2 := (poissonFactorialMoment2_hasSum rate).mul_left (B ^ 2)
    have hfun : (fun j => (poissonMeasure rate).real {j} * ((j : ℝ) * A + (j : ℝ) * ((j : ℝ) - 1) * B ^ 2))
        = fun (j : ℕ) => A * ((j : ℝ) * (poissonMeasure rate).real {j})
          + B ^ 2 * (((j : ℝ) * ((j : ℝ) - 1)) * (poissonMeasure rate).real {j}) := by
      funext j; ring
    rw [hfun]; exact h1.add h2
  rw [hHS.tsum_eq]
  have hr : (rate : ℝ) = (m (prmPiece m k)).toReal := rfl
  have hAeq : (rate : ℝ) * A = ∫ x in prmPiece m k, f x ^ 2 ∂m := by
    rw [hr, hA]; exact toReal_mul_integral_prmPieceLaw (fun x => f x ^ 2)
  have hBeq : (rate : ℝ) * B = ∫ x in prmPiece m k, f x ∂m := by
    rw [hr, hB]; exact toReal_mul_integral_prmPieceLaw f
  rw [mul_comm A (rate : ℝ), hAeq, show B ^ 2 * (rate : ℝ) ^ 2 = ((rate : ℝ) * B) ^ 2 from by ring,
    hBeq]

/-- **Independence of piece sums of distinct pieces.** For `j ≠ k`, the piece sum over piece `j` is
independent of the piece sum over piece `k`: each is a measurable functional of its own block, and
the blocks are independent. -/
theorem indepFun_pieceSum_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g) {j k : ℕ} (hjk : j ≠ k) :
    IndepFun (pieceSum K X f j) (pieceSum K X g k) μ := by
  have hmapf : Measurable fun p : ℕ × (ℕ → E) => ∑ n ∈ Finset.range p.1, f (p.2 n) := by
    have h : Measurable fun p : (ℕ → E) × ℕ => ∑ n ∈ Finset.range p.2, f (p.1 n) :=
      measurable_from_prod_countable_left fun y =>
        Finset.measurable_sum (Finset.range y) fun n _ => hf.comp (measurable_pi_apply n)
    exact h.comp measurable_swap
  have hmapg : Measurable fun p : ℕ × (ℕ → E) => ∑ n ∈ Finset.range p.1, g (p.2 n) := by
    have h : Measurable fun p : (ℕ → E) × ℕ => ∑ n ∈ Finset.range p.2, g (p.1 n) :=
      measurable_from_prod_countable_left fun y =>
        Finset.measurable_sum (Finset.range y) fun n _ => hg.comp (measurable_pi_apply n)
    exact h.comp measurable_swap
  exact (hd.indepFun_piece_piece hjk).comp hmapf hmapg

/-- The sum of the first `n + 1` Poisson pieces is independent of the next
piece. Pairwise independence of piece sums alone would not suffice here; this
uses independence of the underlying count-and-mark blocks. -/
theorem indepFun_pieceSum_prefix_next [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) :
    IndepFun
      (fun ω => ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)
      (pieceSum K X f (n + 1)) μ := by
  let S := {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i ≤ n}
  let T := {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i = n + 1}
  let leftCount (k : Fin (n + 1)) : S :=
    ⟨Sum.inl k.1, by simp [pointFamilyBlock]; omega⟩
  let leftPoint (k : Fin (n + 1)) (j : ℕ) : S :=
    ⟨Sum.inr (k.1, j), by simp [pointFamilyBlock]; omega⟩
  let rightCount : T := ⟨Sum.inl (n + 1), by simp [pointFamilyBlock]⟩
  let rightPoint (j : ℕ) : T :=
    ⟨Sum.inr (n + 1, j), by simp [pointFamilyBlock]⟩
  let leftMap : (∀ i : S, pointFamilyIndexType E i.1) → ℝ := fun g =>
    ∑ k : Fin (n + 1),
      ∑ j ∈ Finset.range (g (leftCount k)), f (g (leftPoint k j))
  let rightMap : (∀ i : T, pointFamilyIndexType E i.1) → ℝ := fun g =>
    ∑ j ∈ Finset.range (g rightCount), f (g (rightPoint j))
  have hleftPiece (k : Fin (n + 1)) : Measurable
      (fun g : ∀ i : S, pointFamilyIndexType E i.1 =>
        ∑ j ∈ Finset.range (g (leftCount k)), f (g (leftPoint k j))) := by
    have h : Measurable
        (fun p : (ℕ → E) × ℕ => ∑ j ∈ Finset.range p.2, f (p.1 j)) :=
      measurable_from_prod_countable_left fun q =>
        Finset.measurable_sum (Finset.range q) fun j _ =>
          hf.comp (measurable_pi_apply j)
    have hp : Measurable (fun g : ∀ i : S, pointFamilyIndexType E i.1 =>
        ((fun j => g (leftPoint k j)), g (leftCount k))) :=
      (Measurable.of_eval fun j => measurable_pi_apply (leftPoint k j)).prodMk
        (measurable_pi_apply (leftCount k))
    exact h.comp hp
  have hleft : Measurable leftMap := by
    exact Finset.measurable_sum _ fun k _ => hleftPiece k
  have hright : Measurable rightMap := by
    have h : Measurable
        (fun p : (ℕ → E) × ℕ => ∑ j ∈ Finset.range p.2, f (p.1 j)) :=
      measurable_from_prod_countable_left fun q =>
        Finset.measurable_sum (Finset.range q) fun j _ =>
          hf.comp (measurable_pi_apply j)
    have hp : Measurable (fun g : ∀ i : T, pointFamilyIndexType E i.1 =>
        ((fun j => g (rightPoint j)), g rightCount)) :=
      (Measurable.of_eval fun j => measurable_pi_apply (rightPoint j)).prodMk
        (measurable_pi_apply rightCount)
    exact h.comp hp
  have h := (hd.indepFun_pieceBlocks n).comp hleft hright
  convert h using 1
  · ext ω
    simp only [Function.comp_apply, leftMap, leftCount, leftPoint, pieceSum,
      pointFamilyCombined]
    rw [← Fin.sum_univ_eq_sum_range
      (fun k : ℕ => ∑ j ∈ Finset.range (K k ω), f (X k j ω)) (n + 1)]
  · ext ω
    rfl
end PieceSum


end ProbabilityTheory
