module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Probability.Process.Levy.Jump.Intensity.Cutoff
public import Probability.Process.Levy.Jump.PoissonConfiguration.Entrance
public import Probability.RandomMeasure.Poisson.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Probability.Process.Levy.Jump.Campbell.Support
import Probability.Process.Levy.Jump.Intensity.TimeMark

@[expose] public section

/-!
# Endpoint of a jump-sum path

At the final observation time, the path defined through selected jump
regions agrees with the sum of the full realized Poisson integrals whenever
the two realized measures are supported by their respective regions.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem poissonEntrancePath_top_eq_integral
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
    (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ)
    (A H : Set (unitInterval × ℝ)) (ω : Ωs × Ωb)
    (hs : (poissonRandomMeasure Ks Xs ω.1).restrict A =
      poissonRandomMeasure Ks Xs ω.1)
    (hb : (poissonRandomMeasure Kb Xb ω.2).restrict H =
      poissonRandomMeasure Kb Xb ω.2) :
    poissonEntrancePath Ks Xs Kb Xb A H ⊤ ω =
      (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  simp only [poissonEntrancePath, poissonJumpPath, le_top, and_true, ite_true]
  change (∫ z, z.2 ∂((poissonRandomMeasure Ks Xs ω.1).restrict A)) +
    (∫ z, z.2 ∂((poissonRandomMeasure Kb Xb ω.2).restrict H)) = _
  rw [hs, hb]

/-- The selected endpoint agrees almost surely with the unrestricted sum
when each source intensity is carried by its selected region. -/
theorem ae_poissonEntrancePath_top_eq_integral
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ms mb : Measure (unitInterval × ℝ)} [SigmaFinite ms] [SigmaFinite mb]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    {A H : Set (unitInterval × ℝ)}
    (hA : MeasurableSet A) (hH : MeasurableSet H)
    (hAs : ms Aᶜ = 0) (hHb : mb Hᶜ = 0) :
    ∀ᵐ ω ∂(Ps.prod Pb),
      poissonEntrancePath Ks Xs Kb Xb A H ⊤ ω =
        (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  have hs0 : ∀ᵐ ω ∂Ps, poissonRandomMeasure Ks Xs ω Aᶜ = 0 := by
    apply (lintegral_eq_zero_iff
      (measurable_poissonRandomMeasure_apply hds.measurable_count
        hds.measurable_point hA.compl)).mp
    exact (lintegral_poissonRandomMeasure_apply hds hA.compl).trans hAs
  have hb0 : ∀ᵐ ω ∂Pb, poissonRandomMeasure Kb Xb ω Hᶜ = 0 := by
    apply (lintegral_eq_zero_iff
      (measurable_poissonRandomMeasure_apply hdb.measurable_count
        hdb.measurable_point hH.compl)).mp
    exact (lintegral_poissonRandomMeasure_apply hdb hH.compl).trans hHb
  have hmeas : MeasurableSet {ω : Ωs × Ωb |
      poissonRandomMeasure Ks Xs ω.1 Aᶜ = 0 ∧
      poissonRandomMeasure Kb Xb ω.2 Hᶜ = 0} := by
    exact ((measurableSet_singleton (x := (0 : ENNReal))).preimage
      ((measurable_poissonRandomMeasure_apply hds.measurable_count
        hds.measurable_point hA.compl).comp measurable_fst)).inter
      ((measurableSet_singleton (x := (0 : ENNReal))).preimage
        ((measurable_poissonRandomMeasure_apply hdb.measurable_count
          hdb.measurable_point hH.compl).comp measurable_snd))
  have hboth : ∀ᵐ ω ∂(Ps.prod Pb),
      poissonRandomMeasure Ks Xs ω.1 Aᶜ = 0 ∧
      poissonRandomMeasure Kb Xb ω.2 Hᶜ = 0 :=
    (Measure.ae_prod_iff_ae_ae hmeas).2 (hs0.mono fun ω hω =>
      hb0.mono fun _ hη => ⟨hω, hη⟩)
  filter_upwards [hboth] with ω hω
  apply poissonEntrancePath_top_eq_integral Ks Xs Kb Xb A H ω
  · apply Measure.restrict_eq_self_of_ae_mem
    change A ∈ ae (poissonRandomMeasure Ks Xs ω.1)
    exact mem_ae_iff.mpr hω.1
  · apply Measure.restrict_eq_self_of_ae_mem
    change H ∈ ae (poissonRandomMeasure Kb Xb ω.2)
    exact mem_ae_iff.mpr hω.2

/-- The fixed-cutoff path used in the entrance construction has the full
small-plus-large jump sum as its unit-time endpoint almost surely. -/
theorem ae_poissonEntrancePath_cutoff_top_eq_integral
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n))) Pb) :
    ∀ᵐ ω ∂(Ps.prod Pb),
      poissonEntrancePath Ks Xs Kb Xb
        (Set.univ ×ˢ smallJumpBand n) (Set.univ ×ˢ largeJumpBand n) ⊤ ω =
        (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  exact ae_poissonEntrancePath_top_eq_integral hds hdb
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_smallJumpBand n))
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_largeJumpBand n))
    (unitTime_prod_restrict_carrier ν (smallJumpBand n) (measurableSet_smallJumpBand n))
    (unitTime_prod_restrict_carrier ν (largeJumpBand n) (measurableSet_largeJumpBand n))

end ProbabilityTheory
