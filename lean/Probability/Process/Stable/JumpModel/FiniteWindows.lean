/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Levy.Jump.Characteristic.FiniteWindows
import Probability.RandomMeasure.Poisson.WindowIntegral
import Probability.Distributions.Stable.LevyMeasure.EndpointLaw

/-!
# Finite-dimensional laws of the cutoff stable jump model

For a finite family of pairwise disjoint time windows, the vector of Poisson
jump integrals has the product of the corresponding stable increment laws.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- For disjoint windows, the cutoff Poisson model has independent stable
increments with the expected clock lengths. -/
theorem IsStrictlyAlphaStable.measure_map_poissonWindowIntegralVector_eq_pi
    {ι : Type*} {Ωs Ωb : Type} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Pb)
    (S : ι → Set unitInterval)
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hsi : ∀ i, ∀ᵐ ω : Ωs ∂Ps, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure (Ω := Ωs) (E := unitInterval × ℝ) Ks Xs ω))
    (hbi : ∀ i, ∀ᵐ ω : Ωb ∂Pb, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure (Ω := Ωb) (E := unitInterval × ℝ) Kb Xb ω)) :
    (Ps.prod Pb).map (poissonWindowIntegralVector
      (Ks := Ks) (Xs := Xs) (Kb := Kb) (Xb := Xb) S) =
      Measure.pi (fun i : ι => μ.map fun x =>
        ((volume : Measure unitInterval) (S i)).toReal ^ (1 / α) * x) := by
  let a : ι → ℝ := fun i => ((volume : Measure unitInterval) (S i)).toReal
  let νi : ι → Measure ℝ := fun i =>
    μ.map fun x => a i ^ (1 / α) * x
  let W : Ωs × Ωb → ι → ℝ := poissonWindowIntegralVector
    (Ks := Ks) (Xs := Xs) (Kb := Kb) (Xb := Xb) S
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hW : AEMeasurable W (Ps.prod Pb) := by
    simpa [W] using poissonWindowIntegralVector_aemeasurable hds hdb S hS hsi hbi
  have hpiProb (i : ι) : IsProbabilityMeasure (νi i) := by
    dsimp [νi]
    infer_instance
  let : ∀ i, IsProbabilityMeasure (νi i) := hpiProb
  have : IsProbabilityMeasure (Measure.pi νi) := by infer_instance
  change (Ps.prod Pb).map W = Measure.pi νi
  apply Measure.ext_of_charFunDual
  funext L
  let u : ι → ℝ := fun i => L (Pi.single i (1 : ℝ))
  have hlinear (ω : Ωs × Ωb) : L (W ω) =
      ∑ i, u i * W ω i := by
    have hrepr := L.toLinearMap.pi_apply_eq_sum_univ (W ω)
    have hbasis (i : ι) : (fun j : ι => if i = j then (1 : ℝ) else 0) =
        Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply, eq_comm]
    rw [show L (W ω) = L.toLinearMap (W ω) from rfl, hrepr]
    simp only [hbasis, u, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp [mul_comm]
  have hsmall : Integrable smallJumpDisplacement T.levyMeasure :=
    integrable_smallJumpDisplacement (h.levyMeasure_integrableOn_small T hT hα)
  have hcombo (ω : Ωs × Ωb) :
      (∑ i, u i * W ω i) =
        finiteWindowIntegral S u (poissonRandomMeasure Ks Xs ω.1) +
          finiteWindowIntegral S u (poissonRandomMeasure Kb Xb ω.2) := by
    simp only [W, poissonWindowIntegralVector, finiteWindowIntegral]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hleft : charFunDual ((Ps.prod Pb).map W) L =
      Complex.exp (∑ i, a i •
        (∫ x, levyUncompensatedIntegrand (u i) x ∂T.levyMeasure)) := by
    rw [charFunDual_apply, integral_map hW (by fun_prop)]
    calc
      (∫ ω : Ωs × Ωb, Complex.exp (L (W ω) * Complex.I) ∂(Ps.prod Pb)) =
          ∫ ω : Ωs × Ωb, Complex.exp
            (((finiteWindowIntegral S u (poissonRandomMeasure Ks Xs ω.1) +
              finiteWindowIntegral S u (poissonRandomMeasure Kb Xb ω.2) : ℝ) : ℂ) *
              Complex.I) ∂(Ps.prod Pb) := by
            apply integral_congr_ae
            filter_upwards with ω
            rw [hlinear ω, hcombo ω]
      _ = Complex.exp (∑ i, a i •
            (∫ x, levyUncompensatedIntegrand (u i) x ∂T.levyMeasure)) := by
          simpa [finiteWindowIntegral] using
            T.isLevyMeasure.integral_exp_finiteWindowIntegrals_cutoff_poissonRandomMeasures
              hsmall n hds hdb S u hS hdisj 1 hsi hbi
  have hfactor (i : ι) :
      charFunDual (νi i) (L.comp (.single ℝ (fun _ : ι => ℝ) i)) =
        Complex.exp (a i • T.exponent (u i)) := by
    let Li : StrongDual ℝ ℝ := L.comp (.single ℝ (fun _ : ι => ℝ) i)
    have hsingle (x : ℝ) :
        Li x = u i * x := by
      change L (Pi.single i x) = u i * x
      have hrepr : Pi.single i x = x • Pi.single i (1 : ℝ) := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      rw [hrepr, map_smul]
      rw [show L (Pi.single i (1 : ℝ)) = u i by rfl]
      ring
    have hcomp :
        Li ∘
          (fun x : ℝ => a i ^ (1 / α) * x) =
            fun x => (a i ^ (1 / α) * u i) * x := by
      funext x
      change Li (a i ^ (1 / α) * x) = _
      rw [hsingle]
      ring
    have hmap : (νi i).map Li =
        μ.map (fun x => (a i ^ (1 / α) * u i) * x) := by
      dsimp [νi]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
    calc
      charFunDual (νi i) Li = charFun ((νi i).map Li) 1 :=
        charFunDual_eq_charFun_map_one Li
      _ = charFun (μ.map (fun x => (a i ^ (1 / α) * u i) * x)) 1 := by rw [hmap]
      _ = charFun μ (a i ^ (1 / α) * u i) := by
        rw [charFun_map_mul]
        congr 1
        ring
      _ = Complex.exp (T.exponent (a i ^ (1 / α) * u i)) := hT _
      _ = Complex.exp (a i • T.exponent (u i)) := by
        rw [h.exponent_time T hT (ENNReal.toReal_nonneg) (u i)]
        have hsmul (z : ℂ) :
            (a i : ℂ) * z = (a i : ℝ) • z := by
          simp [Complex.real_smul]
        exact congrArg Complex.exp (hsmul (T.exponent (u i)))
  calc
    charFunDual ((Ps.prod Pb).map W) L =
        Complex.exp (∑ i, a i •
          (∫ x, levyUncompensatedIntegrand (u i) x ∂T.levyMeasure)) := hleft
    _ = ∏ i, Complex.exp (a i • T.exponent (u i)) := by
      have hsum : (∑ i, a i •
          (∫ x, levyUncompensatedIntegrand (u i) x ∂T.levyMeasure)) =
          ∑ i, a i • T.exponent (u i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← h.exponent_eq_integral_uncompensated T hT hα (u i)]
      rw [hsum, Complex.exp_sum]
    _ = ∏ i, charFunDual (νi i)
          (L.comp (.single ℝ (fun _ : ι => ℝ) i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hfactor i).symm
    _ = charFunDual (Measure.pi νi) L := (charFunDual_pi L).symm

end ProbabilityTheory

end
