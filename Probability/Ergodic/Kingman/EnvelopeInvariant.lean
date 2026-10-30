/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

public import Probability.Ergodic.Kingman.Basic
import Probability.Ergodic.Invariant
import all Probability.Ergodic.Kingman.Lemmas.Companion
import all Probability.Ergodic.Kingman.Lemmas.FatouEnvelope
import Order.Filter.LiminfLimsup

/-!
# Almost-everywhere invariance of the Kingman liminf envelope

For an integrable subadditive cocycle over a finite measure-preserving map,
the normalized liminf envelope is almost-everywhere invariant once its values
are bounded below almost everywhere. The pointwise shift comparison used in
the proof is private to this module.

## Public declarations

* `ProbabilityTheory.Kingman.liminf_div_comp_ae`: if `T` preserves the finite
  measure \(\mu\), \(g\) is an integrable subadditive cocycle, and
  \(g(n+1,x)/(n+1)\) is bounded below in \(n\) for \(\mu\)-almost every
  \(x\), then
  \[
    \liminf_{n\to\infty}\frac{g(n+1,T x)}{n+1}
      =\liminf_{n\to\infty}\frac{g(n+1,x)}{n+1}
    \quad\text{for }\mu\text{-almost every }x.
  \]

## References

* The liminf-envelope part of Proposition 3.3 in Anders Karlsson, “A Proof of
  the Subadditive Ergodic Theorem,” Chapter 12 in *Groups, Graphs and Random
  Walks*, London Mathematical Society Lecture Note Series 436, Cambridge
  University Press (2017), pp. 343–354, DOI 10.1017/9781316576571.014.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

omit [MeasurableSpace X] in
/-- For a fixed `x` where the normalized cocycle is bounded above and below
along both the orbit of `x` and the orbit of `T x`,
`liminfₙ cdiv g n x ≤ liminfₙ cdiv g n (T x)`. -/
private lemma liminf_cdiv_le_comp {g : ℕ → X → ℝ} (hsub : IsSubadditiveCocycle T g) {x : X}
    (_hax : BddAbove (Set.range fun n : ℕ => cdiv g n x))
    (hbx : BddBelow (Set.range fun n : ℕ => cdiv g n x))
    (haTx : BddAbove (Set.range fun n : ℕ => cdiv g n (T x)))
    (hbTx : BddBelow (Set.range fun n : ℕ => cdiv g n (T x))) :
    Filter.liminf (fun n => cdiv g n x) atTop ≤ Filter.liminf (fun n => cdiv g n (T x)) atTop := by
  set target : ℕ → ℝ := fun n => cdiv g n (T x) with htdef
  set w : ℕ → ℝ := fun n => g 1 x / (n + 1) + g n (T x) / (n + 1) with hwdef
  have hcw : ∀ n, cdiv g n x ≤ w n := fun n => cdiv_le_shift hsub n x
  set w' : ℕ → ℝ := fun m => w (m + 1) with hw'def
  have hdiff : Tendsto (fun m => w' m - target m) atTop (𝓝 0) := by
    have hform : ∀ m : ℕ, w' m - target m
        = g 1 x / ((m : ℝ) + 2) - target m / ((m : ℝ) + 2) := by
      intro m
      simp only [hw'def, hwdef, htdef, cdiv]
      have h1 : (((m : ℕ) + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
      rw [h1]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
    refine Tendsto.congr (fun m => (hform m).symm) ?_
    have hinv2 : Tendsto (fun m : ℕ => ((m : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact tendsto_inv_atTop_zero.comp this
    have ht1 : Tendsto (fun m : ℕ => g 1 x / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      simp only [div_eq_mul_inv]
      simpa using hinv2.const_mul (g 1 x)
    have ht2 : Tendsto (fun m : ℕ => target m / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      obtain ⟨Ma, hMa⟩ := haTx; obtain ⟨mb, hmb⟩ := hbTx
      have hnorm : IsBoundedUnder (· ≤ ·) atTop (norm ∘ target) := by
        refine ⟨|mb| + |Ma|, ?_⟩
        simp only [eventually_map]
        filter_upwards with m
        have h1 := hmb (Set.mem_range_self m); have h2 := hMa (Set.mem_range_self m)
        simp only [Function.comp_apply, Real.norm_eq_abs, abs_le]
        constructor
        · nlinarith [neg_abs_le mb, le_abs_self Ma, abs_nonneg mb, abs_nonneg Ma]
        · nlinarith [le_abs_self Ma, neg_abs_le mb, abs_nonneg mb, abs_nonneg Ma]
      have := Filter.isBoundedUnder_le_mul_tendsto_zero hnorm hinv2
      simpa only [div_eq_mul_inv] using this
    simpa using ht1.sub ht2
  have htargetA : BddAbove (Set.range target) := haTx
  have htargetB : BddBelow (Set.range target) := hbTx
  have hw'A : BddAbove (Set.range w') := by
    obtain ⟨C, hC⟩ := (hdiff.bddAbove_range)
    obtain ⟨Mt, hMt⟩ := htargetA
    refine ⟨Mt + C, ?_⟩
    rintro y ⟨m, rfl⟩
    have h1 : target m ≤ Mt := hMt (Set.mem_range_self m)
    have h2 : w' m - target m ≤ C := hC (Set.mem_range_self m)
    linarith
  have hw'B : BddBelow (Set.range w') := by
    obtain ⟨c, hc⟩ := (hdiff.bddBelow_range)
    obtain ⟨mt, hmt⟩ := htargetB
    refine ⟨mt + c, ?_⟩
    rintro y ⟨m, rfl⟩
    have h1 : mt ≤ target m := hmt (Set.mem_range_self m)
    have h2 : c ≤ w' m - target m := hc (Set.mem_range_self m)
    linarith
  have hwA : BddAbove (Set.range w) := by
    obtain ⟨M', hM'⟩ := hw'A
    refine ⟨max M' (w 0), ?_⟩
    rintro y ⟨n, rfl⟩
    rcases n with _ | m
    · exact le_max_right _ _
    · exact le_trans (hM' (Set.mem_range_self m)) (le_max_left _ _)
  have hwB : BddBelow (Set.range w) := by
    obtain ⟨m', hm'⟩ := hw'B
    refine ⟨min m' (w 0), ?_⟩
    rintro y ⟨n, rfl⟩
    rcases n with _ | m
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hm' (Set.mem_range_self m))
  have hstepA : Filter.liminf (fun n => cdiv g n x) atTop ≤ Filter.liminf w atTop := by
    refine Filter.liminf_le_liminf (Eventually.of_forall hcw) ?_ ?_
    · exact hbx.isBoundedUnder_of_range
    · exact hwA.isBoundedUnder_of_range.isCoboundedUnder_ge
  have hww' : Filter.liminf w atTop = Filter.liminf w' atTop := (liminf_nat_add w 1).symm
  have hw'target : Filter.liminf w' atTop = Filter.liminf target atTop :=
    Filter.liminf_eq_of_sub_tendsto_zero
      hw'A.isBoundedUnder_of_range hw'B.isBoundedUnder_of_range
      htargetA.isBoundedUnder_of_range htargetB.isBoundedUnder_of_range hdiff
  calc Filter.liminf (fun n => cdiv g n x) atTop
      ≤ Filter.liminf w atTop := hstepA
    _ = Filter.liminf target atTop := hww'.trans hw'target

/-- **Liminf-envelope invariance.** The normalized liminf of an integrable
subadditive cocycle is a.e. invariant under a finite measure-preserving map,
provided the normalized cocycle is bounded below almost everywhere. -/
theorem liminf_div_comp_ae [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbelow : ∀ᵐ x ∂μ, BddBelow (Set.range fun n : ℕ => cdiv g n x)) :
    (fun x => Filter.liminf (fun n => cdiv g n x) atTop) ∘ T
      =ᵐ[μ] fun x => Filter.liminf (fun n => cdiv g n x) atTop := by
  have hax := ae_bddAbove_cdiv hT hsub hint
  have hbx := hbelow
  have haTx := hT.quasiMeasurePreserving.tendsto_ae hax
  have hbTx := hT.quasiMeasurePreserving.tendsto_ae hbx
  refine ae_eq_comp_of_le_comp hT (aemeasurable_liminf_div hint) ?_
  filter_upwards [hax, hbx, haTx, hbTx] with x hax hbx haTx hbTx
  exact liminf_cdiv_le_comp hsub hax hbx haTx hbTx

end ProbabilityTheory.Kingman

end
