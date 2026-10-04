/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.Levy.Jump.PoissonConfiguration.Entrance

/-!
# Entrance after a fixed Lévy-intensity cutoff

Here the small and large Poisson sources already carry the two restricted
intensities. A strict first-moment bound on the small source yields the
positive entrance event without a further truncation of its realized path.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem exists_poissonEntrancePath_model_of_smallMoment
    (ms mb : Measure (unitInterval × ℝ))
    [SigmaFinite ms] [SigmaFinite mb]
    {J B : Set (unitInterval × ℝ)}
    (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : mb J < ⊤) (hfinB : mb B < ⊤)
    (hJpos : 0 < mb J) (hdisj : Disjoint J B)
    (lower upper target ρ ε margin : ℝ)
    (hsmallMoment :
      (∫⁻ z, ENNReal.ofReal |z.2| ∂ms) < ENNReal.ofReal ρ)
    (hρ : 0 < ρ) (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hJwindow : ∀ z ∈ J, |z.2 - target| < ρ) :
    ∃ (Ωs Ωb : Type) (_ : MeasurableSpace Ωs) (_ : MeasurableSpace Ωb)
      (Ps : Measure Ωs) (Pb : Measure Ωb)
      (Ks : ℕ → Ωs → ℕ)
      (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
      (Kb : ℕ → Ωb → ℕ)
      (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ),
      IsProbabilityMeasure Ps ∧ IsProbabilityMeasure Pb ∧
      IsPoissonPointFamily Ks Xs ms Ps ∧
      IsPoissonPointFamily Kb Xb mb Pb ∧
      0 < (Ps.prod Pb) {ω : Ωs × Ωb |
        (∀ t, lower + (margin - 2 * ρ) ≤
            poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) t ω ∧
          poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) t ω ≤
            upper - (margin - 2 * ρ)) ∧
        target - ε < poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) ⊤ ω ∧
        poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) ⊤ ω < target + ε} := by
  obtain ⟨Ωs, mΩs, Ps, Ks, Xs, hPs, hds⟩ := exists_isPoissonPointFamily ms
  obtain ⟨Ωb, mΩb, Pb, Kb, Xb, hPb, hdb⟩ := exists_isPoissonPointFamily mb
  let := mΩs
  let := mΩb
  let := hPs
  let := hPb
  let V : Ωs → ENNReal := fun ω =>
    ∫⁻ z, ENNReal.ofReal |z.2| ∂(poissonRandomMeasure Ks Xs ω)
  have hV : Measurable V :=
    measurable_lintegral_poissonRandomMeasure
      hds.measurable_count hds.measurable_point (by fun_prop)
  have hE : (∫⁻ ω, V ω ∂Ps) < ENNReal.ofReal ρ := by
    rw [lintegral_lintegral_poissonRandomMeasure hds (by fun_prop)]
    exact hsmallMoment
  have hsmall : 0 < Ps {ω | V ω < ENNReal.ofReal ρ} :=
    measure_smallVariation_pos Ps V hV (ENNReal.ofReal ρ) hE
  have hbig := measure_poissonRandomMeasure_one_and_zero_pos
    hdb hJ hB hfinJ hfinB hJpos hdisj
  have hgood : 0 < (Ps.prod Pb) {ω : Ωs × Ωb |
      (∫⁻ z in Set.univ, ENNReal.ofReal |z.2|
        ∂(poissonRandomMeasure Ks Xs ω.1)) < ENNReal.ofReal ρ ∧
      (poissonRandomMeasure Kb Xb ω.2 : Measure (unitInterval × ℝ)) J = 1 ∧
      (poissonRandomMeasure Kb Xb ω.2 : Measure (unitInterval × ℝ)) B = 0} := by
    have hset : {ω : Ωs × Ωb |
        (∫⁻ z in Set.univ, ENNReal.ofReal |z.2|
          ∂(poissonRandomMeasure Ks Xs ω.1)) < ENNReal.ofReal ρ ∧
        poissonRandomMeasure Kb Xb ω.2 J = 1 ∧
        poissonRandomMeasure Kb Xb ω.2 B = 0} =
        {ω : Ωs | V ω < ENNReal.ofReal ρ} ×ˢ
        {ω : Ωb | poissonRandomMeasure Kb Xb ω J = 1 ∧
          poissonRandomMeasure Kb Xb ω B = 0} := by
      ext ω
      simp [V]
    rw [hset, Measure.prod_prod]
    exact ENNReal.mul_pos hsmall.ne' hbig.ne'
  refine ⟨Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
    hPs, hPb, hds, hdb, ?_⟩
  exact measure_poissonEntrancePath_pos_of_one_zero
    (mb := mb) Ps Pb Set.univ J B hJ hB
    lower upper target ρ ε margin hρ hε hl0 hu0 hly huy
    hJwindow hgood

end ProbabilityTheory
