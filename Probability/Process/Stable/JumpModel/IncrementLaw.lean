import Probability.Distributions.Stable.LevyMeasure.EndpointLaw
import Probability.Process.Levy.Jump.PoissonConfiguration.Increment

/-!
# Increment law of the finite-variation stable jump model

The actual selected Poisson path has the prescribed strictly stable law on
each deterministic time interval. This identifies one increment at a time;
the joint law of several disjoint intervals is proved separately.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem IsStrictlyAlphaStable.law_poissonEntrancePath_cutoff_increment
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
    (s t : unitInterval) (hst : s ≤ t) :
    (Ps.prod Pb).map (fun ω : Ωs × Ωb =>
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) t ω -
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) s ω) =
      μ.map (fun x => (((volume : Measure unitInterval) (Set.Ioc s t)).toReal ^
        (1 / α)) * x) := by
  have hsfirst := h.integrable_unitTime_smallJumpMark T hT hα n
  rw [Measure.map_congr (ae_poissonEntrancePath_cutoff_sub_eq_timeWindow
    n hds hdb hsfirst (T.levyMeasure_largeJumpBand_lt_top n) s t hst)]
  simpa only [Set.mem_Ioc] using
    (h.law_timeWindow_split_poissonRandomMeasures T hT hα n hds hdb
      (Set.Ioc s t) measurableSet_Ioc)

end ProbabilityTheory
