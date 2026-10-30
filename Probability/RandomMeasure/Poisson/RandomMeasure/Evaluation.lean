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

import Probability.Distributions.Poisson.Moments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import all Probability.RandomMeasure.Poisson.RandomMeasure.Lemmas

/-!
# Evaluation laws of a Poisson random measure

This module proves the intensity identity, the Poisson law of counts on finite-mass measurable sets,
and the first-moment formula for those counts.

For a Poisson point family on a probability space and measurable `A`,
`∫⁻ ω, poissonRandomMeasure K X ω A ∂μ = m A`. If `m A < ⊤`, then
`μ.map (fun ω => poissonRandomMeasure K X ω A) =
  (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)`;
the real-valued count is integrable and has integral `(m A).toReal`.

## Public declarations

- `lintegral_poissonRandomMeasure_apply` says the expected count in measurable $A$ is $m(A)$.
- `map_poissonRandomMeasure_apply` states that the count in finite-mass $A$ has the Poisson law of
  parameter $(m(A)).toNNReal$.
- `ae_poissonRandomMeasure_apply_lt_top` proves the count is almost surely finite when $m(A)<\infty$.
- `integrable_toReal_poissonRandomMeasure_apply` and `integral_toReal_poissonRandomMeasure_apply`
  give integrability and mean $(m(A)).toReal$ of the real-valued count.
-/

@[expose] public section

open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m]
    [Nonempty E] {μ : Measure Ω} {A B : Set E} {ω : Ω}

/-! ### Superposition: the law of the count in a set

The count of realized points in a measurable set `A` is the superposition `∑ₖ thinnedCount K X A k`
of the per-piece thinned counts. Its partial sums `prmPartialCount K X A n` are Poisson-distributed
(by convolution, using the prefix-versus-next-block independence of the point family), and passing to
the limit — legitimate because the total count is almost surely finite, with `E[count] = m A < ⊤` —
identifies the count in `A` as Poisson with mean `m A`. -/


/-- The `ℝ≥0∞`-mean of the thinned count is the mass of the piece intersected with `A`. -/
private lemma lintegral_thinnedCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) :
    ∫⁻ ω, (thinnedCount K X A k ω : ℝ≥0∞) ∂μ = m (prmPiece m k ∩ A) := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  have hmap : ∫⁻ ω, (thinnedCount K X A k ω : ℝ≥0∞) ∂μ
      = ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂(μ.map (thinnedCount K X A k)) :=
    (lintegral_map (f := fun n : ℕ => (n : ℝ≥0∞)) measurable_from_top hTA).symm
  rw [hmap, map_thinnedCount hd hA, lintegral_id_poissonMeasure,
    ENNReal.coe_toNNReal (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      measure_prmPiece_lt_top).ne]

/-- **Evaluation mean of the Poisson random measure.** The total count in a measurable set `A` has
`ℝ≥0∞`-mean equal to the intensity `m A` (both sides may be `⊤`). -/
theorem lintegral_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) :
    ∫⁻ ω, poissonRandomMeasure K X ω A ∂μ = m A := by
  simp_rw [poissonRandomMeasure_apply hA]
  rw [lintegral_tsum (f := fun k ω => (thinnedCount K X A k ω : ℝ≥0∞)) fun k =>
    (measurable_from_top.comp
      (measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA)).aemeasurable]
  simp_rw [lintegral_thinnedCount hd hA]
  exact tsum_measure_prmPiece_inter hA

/-- The total count in a finite-mass set is almost surely finite. -/
theorem ae_poissonRandomMeasure_apply_lt_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    ∀ᵐ ω ∂μ, poissonRandomMeasure K X ω A < ⊤ :=
  ae_lt_top (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA)
    (by rw [lintegral_poissonRandomMeasure_apply hd hA]; exact hfin.ne)


/-- **Prefix-versus-next-piece independence of the superposition count.** The partial count from the
first `n + 1` pieces is independent of the thinned count of piece `n + 1`, since they read disjoint
blocks of the point family. -/
private lemma indepFun_prmPartialCount_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (n : ℕ) :
    IndepFun (prmPartialCount K X A n) (thinnedCount K X A (n + 1)) μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ)) (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1)) (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;>
      simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;> simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
      ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := hd.indepFun_pointFamily_split φ ψ hφ_inj hψ_inj hST
  -- Extraction of the prefix count from the left block process.
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType E (φ i)) → ℕ :=
    fun g => ∑ k : Fin (n + 1),
      ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ A).card with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType E (ψ j)) → ℕ :=
    fun g => ((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ A).card with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact Finset.measurable_sum _ fun k _ =>
      measurable_filterCard
        (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        hA (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H := by
    rw [hH_def]
    exact measurable_filterCard
      (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
      hA (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
      (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω) = prmPartialCount K X A n := by
    funext ω
    simp only [hG_def]
    unfold prmPartialCount
    rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X A j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω)
      = thinnedCount K X A (n + 1) := by
    funext ω; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rwa [hGeq, hHeq] at key

/-- **The partial superposition count is Poisson.** The count of points landing in `A` from the first
`n + 1` pieces is Poisson-distributed with mean `∑ₖ m (piece k ∩ A)`. Proved by induction on `n`:
each new piece contributes an independent thinned count, and Poisson laws convolve by adding rates. -/
private lemma map_prmPartialCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (n : ℕ) :
    μ.map (prmPartialCount K X A n)
      = poissonMeasure (∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal) := by
  induction n with
  | zero =>
    have h0 : prmPartialCount K X A 0 = thinnedCount K X A 0 := by
      funext ω; rw [prmPartialCount, Finset.sum_range_one]
    rw [h0, map_thinnedCount hd hA, Finset.sum_range_one]
  | succ n ih =>
    have hsucc : prmPartialCount K X A (n + 1)
        = prmPartialCount K X A n + thinnedCount K X A (n + 1) := by
      funext ω; simp only [prmPartialCount, Pi.add_apply, Finset.sum_range_succ]
    have hlawP : HasLaw (prmPartialCount K X A n)
        (poissonMeasure (∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal)) μ :=
      ⟨(measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n).aemeasurable, ih⟩
    have hlawT : HasLaw (thinnedCount K X A (n + 1))
        (poissonMeasure (m (prmPiece m (n + 1) ∩ A)).toNNReal) μ :=
      ⟨(measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) hA).aemeasurable,
        map_thinnedCount hd hA⟩
    have hsum := (indepFun_prmPartialCount_thinnedCount hd hA n).hasLaw_add hlawP hlawT
    rw [hsucc, hsum.map_eq, poissonMeasure_conv_poissonMeasure]
    congr 1
    exact (Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ A)).toNNReal) (n + 1)).symm

/-! ### The superposition law: the count in a finite-mass set is Poisson

The partial counts `prmPartialCount K X A n` increase to the total count `poissonRandomMeasure K X · A`
almost surely (the total count being finite by `ae_poissonRandomMeasure_apply_lt_top`), so their
Poisson laws pass to the limit. The identification is carried out through characteristic functions and
dominated convergence: the characteristic function of each partial count is the Poisson pgf with the
accumulated rate `∑_{k ≤ n} m (piece k ∩ A)`, and these rates increase to `m A`. -/

/-- The characteristic function of the `ℝ`-pushforward of the partial superposition count is the
Poisson pgf with the accumulated rate `∑_{k ≤ n} m (piece k ∩ A)`, read off `map_prmPartialCount`. -/
private lemma charFun_natCast_prmPartialCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (n : ℕ) (ξ : ℝ) :
    charFun (μ.map fun ω => (prmPartialCount K X A n ω : ℝ)) ξ
      = Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
          * (Complex.exp (↑ξ * I) - 1)) := by
  have hmeas := measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n
  have hcoe : ((∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal : ℝ≥0) : ℝ)
      = ∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal := by
    rw [NNReal.coe_sum]
    exact Finset.sum_congr rfl fun k _ => ENNReal.coe_toNNReal_eq_toReal _
  rw [show (fun ω => ((prmPartialCount K X A n ω : ℕ) : ℝ))
        = (Nat.cast : ℕ → ℝ) ∘ prmPartialCount K X A n from rfl,
    ← Measure.map_map measurable_from_top hmeas, map_prmPartialCount hd hA n,
    charFun_map_cast_poissonMeasure, hcoe]


/-- The characteristic function of the `ℝ`-pushforward of the total count in a finite-mass set `A` is
the Poisson pgf with mean `m A`. Obtained by dominated convergence from the partial counts: their
characteristic functions are the Poisson pgfs at the accumulated rates (`charFun_natCast_prmPartialCount`),
the rates increase to `m A` (`tendsto_rate_prmPartialCount`), and the integrands are bounded by `1`
and converge almost surely (`tendsto_natCast_prmPartialCount`). -/
private lemma charFun_natCast_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) (ξ : ℝ) :
    charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ
      = Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)) := by
  have hSn_meas : ∀ n, Measurable fun ω => (prmPartialCount K X A n ω : ℝ) := fun n =>
    measurable_from_top.comp
      (measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n)
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have hFmeas : ∀ n, Measurable
      fun ω => Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I) := fun n =>
    Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp (hSn_meas n)).const_mul (↑ξ)).mul_const I)
  have hbound : ∀ n, ∀ᵐ ω ∂μ,
      ‖Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := by
    intro n
    filter_upwards with ω
    have : ‖Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)‖ = 1 := by
      rw [show (↑ξ : ℂ) * ↑(prmPartialCount K X A n ω : ℝ) * I
          = ↑(ξ * (prmPartialCount K X A n ω : ℝ)) * I from by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    exact le_of_eq this
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun n => Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)) atTop
        (𝓝 (Complex.exp (↑ξ * ↑(poissonRandomMeasure K X ω A).toReal * I))) := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfin] with ω hω
    have hc : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * I) := by fun_prop
    exact (hc.tendsto _).comp (tendsto_natCast_prmPartialCount hA ω hω)
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1 : ℝ)) (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have key : ∀ n, ∫ ω, Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I) ∂μ
      = charFun (μ.map fun ω => (prmPartialCount K X A n ω : ℝ)) ξ := fun n => by
    rw [charFun_apply_real, integral_map (hSn_meas n).aemeasurable (by fun_prop)]
  have keyN : ∫ ω, Complex.exp (↑ξ * ↑(poissonRandomMeasure K X ω A).toReal * I) ∂μ
      = charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ := by
    rw [charFun_apply_real, integral_map hN_meas.aemeasurable (by fun_prop)]
  simp_rw [key, charFun_natCast_prmPartialCount hd hA] at hdct
  rw [keyN] at hdct
  have hrate : Tendsto
      (fun n => Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
        * (Complex.exp (↑ξ * I) - 1))) atTop
      (𝓝 (Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)))) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
      Complex.exp (↑r * (Complex.exp (↑ξ * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount hA hfin)
  exact tendsto_nhds_unique hdct hrate

/-- The `ℝ`-valued count pushes forward to the `ℕ`-cast of the Poisson law of mean `m A`: the
pushforward `μ.map (fun ω => (poissonRandomMeasure K X ω A).toReal)` equals
`(poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ)`. This is the characteristic-function
identification underlying the superposition law, kept as a standalone lemma so that both the
`ℝ≥0∞`-valued law and the real integrability/mean lemmas can reuse it. -/
private lemma map_toReal_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal)
      = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ) := by
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_natCast_poissonRandomMeasure_apply hd hA hfin, charFun_map_cast_poissonMeasure,
    ENNReal.coe_toNNReal_eq_toReal]

/-- **Superposition (the evaluation law).** The total number of realized points landing in a
finite-mass measurable set `A` is Poisson-distributed with mean `m A`. This is the defining property
of a Poisson random measure. The `ℝ≥0∞`-valued count is identified via its `ℝ`-pushforward, whose
characteristic function matches the Poisson pgf (`charFun_natCast_poissonRandomMeasure_apply`), and
then descended along `ENNReal.ofReal` using the almost-sure finiteness of the count. -/
theorem map_poissonRandomMeasure_apply [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (hfin : m A < ⊤) :
    μ.map (fun ω => poissonRandomMeasure K X ω A)
      = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have hRlaw := map_toReal_poissonRandomMeasure_apply hd hA hfin
  have hae : (fun ω => poissonRandomMeasure K X ω A)
      =ᵐ[μ] fun ω => ENNReal.ofReal ((poissonRandomMeasure K X ω A).toReal) := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfin] with ω hω
    rw [ENNReal.ofReal_toReal hω.ne]
  rw [Measure.map_congr hae,
    show (fun ω => ENNReal.ofReal ((poissonRandomMeasure K X ω A).toReal))
      = ENNReal.ofReal ∘ fun ω => (poissonRandomMeasure K X ω A).toReal from rfl,
    ← Measure.map_map ENNReal.continuous_ofReal.measurable hN_meas, hRlaw,
    Measure.map_map ENNReal.continuous_ofReal.measurable measurable_from_top]
  congr 1
  funext n
  rw [Function.comp_apply, ENNReal.ofReal_natCast]

/-- The `ℝ`-valued count in a finite-mass set is integrable. -/
theorem integrable_toReal_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Integrable (fun ω => (poissonRandomMeasure K X ω A).toReal) μ := by
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have h1 : Integrable (id : ℝ → ℝ)
      (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) := by
    rw [map_toReal_poissonRandomMeasure_apply hd hA hfin,
      integrable_map_measure aestronglyMeasurable_id measurable_from_top.aemeasurable]
    exact integrable_id_poissonMeasure _
  exact (integrable_map_measure aestronglyMeasurable_id hN_meas.aemeasurable).mp h1

/-- The `ℝ`-valued count in a finite-mass set has mean `(m A).toReal`. -/
theorem integral_toReal_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    ∫ ω, (poissonRandomMeasure K X ω A).toReal ∂μ = (m A).toReal := by
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  calc ∫ ω, (poissonRandomMeasure K X ω A).toReal ∂μ
      = ∫ y : ℝ, y ∂(μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) :=
        (integral_map hN_meas.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ y : ℝ, y ∂((poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ)) := by
        rw [map_toReal_poissonRandomMeasure_apply hd hA hfin]
    _ = ∫ n : ℕ, (n : ℝ) ∂(poissonMeasure (m A).toNNReal) :=
        integral_map measurable_from_top.aemeasurable aestronglyMeasurable_id
    _ = (m A).toReal := by
        rw [integral_id_poissonMeasure, ENNReal.coe_toNNReal_eq_toReal]


end ProbabilityTheory
