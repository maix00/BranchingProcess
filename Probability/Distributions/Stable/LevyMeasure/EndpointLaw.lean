import Probability.Distributions.Stable.LevyMeasure.Drift
import Probability.Distributions.Stable.LevyMeasure.Cutoff
import Probability.Process.Levy.Jump.Characteristic.TimeMark
import Probability.Process.Levy.Jump.PoissonConfiguration.Endpoint

/-!
# Endpoint law of the stable jump-sum model

For an index below one, every fixed small/large jump cutoff yields the
given strictly stable law at unit time. The proof uses the uncompensated
characteristic exponent and imposes no moment on the large jumps.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem IsStrictlyAlphaStable.law_unitTime_split_poissonRandomMeasures
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
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
        (T.levyMeasure.restrict (largeJumpBand n))) Pb) :
    (Ps.prod Pb).map (fun ω : Ωs × Ωb =>
      (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2))) = μ := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hsmall : Integrable smallJumpDisplacement T.levyMeasure :=
    integrable_smallJumpDisplacement (h.levyMeasure_integrableOn_small T hT hα)
  have hsfirst : Integrable (fun z : unitInterval × ℝ => z.2)
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) :=
    h.integrable_unitTime_smallJumpMark T hT hα n
  exact ProbabilityTheory.law_unitTime_split_poissonRandomMeasures
    T.levyMeasure_isLevyMeasure hsmall n hds hdb hsfirst
    (T.levyMeasure_largeJumpBand_lt_top n)
    (h.charFun_eq_exp_integral_uncompensated T hT hα)

/-- The endpoint of the actual cutoff path in the one-jump entrance
construction has the prescribed stable law. -/
theorem IsStrictlyAlphaStable.law_poissonEntrancePath_cutoff_top
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
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
        (T.levyMeasure.restrict (largeJumpBand n))) Pb) :
    (Ps.prod Pb).map (poissonEntrancePath Ks Xs Kb Xb
      (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) ⊤) = μ := by
  rw [Measure.map_congr (ae_poissonEntrancePath_cutoff_top_eq_integral n hds hdb)]
  exact h.law_unitTime_split_poissonRandomMeasures T hT hα n hds hdb

/-- For every measurable time window, the cutoff jump-sum has the stable
law at the window's elapsed clock mass. This is a one-increment law; joint
laws of disjoint windows require an additional independence argument. -/
theorem IsStrictlyAlphaStable.law_timeWindow_split_poissonRandomMeasures
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1)
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
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
    (S : Set unitInterval) (hS : MeasurableSet S) :
    (Ps.prod Pb).map (fun ω : Ωs × Ωb =>
      (∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, (if z.1 ∈ S then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2))) =
      μ.map (fun x => (((volume : Measure unitInterval) S).toReal ^ (1 / α)) * x) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hsmall : Integrable smallJumpDisplacement T.levyMeasure :=
    integrable_smallJumpDisplacement (h.levyMeasure_integrableOn_small T hT hα)
  have hsfirst : Integrable (fun z : unitInterval × ℝ => z.2)
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (smallJumpBand n))) :=
    h.integrable_unitTime_smallJumpMark T hT hα n
  apply ProbabilityTheory.law_timeWindow_split_poissonRandomMeasures
    T.levyMeasure_isLevyMeasure hsmall n hds hdb hsfirst
    (T.levyMeasure_largeJumpBand_lt_top n) S hS
  intro ξ
  let τ : ℝ := ((volume : Measure unitInterval) S).toReal
  have hτ : 0 ≤ τ := ENNReal.toReal_nonneg
  rw [charFun_map_mul, hT, h.exponent_time T hT hτ ξ,
    h.exponent_eq_integral_uncompensated T hT hα ξ]
  simp only [τ, Complex.real_smul]

end ProbabilityTheory
