import Probability.Process.Levy.Jump.Intensity.Entrance
import Probability.Process.Levy.Jump.PoissonConfiguration.Entrance.FixedCutoff

/-!
# Canonical entrance model for a split Lévy intensity

The target mark window and its complement partition all large jumps. Thus
the positive corridor event below concerns the complete small-plus-large
Poisson jump path at a fixed cutoff, rather than a selected subpath.
-/

namespace ProbabilityTheory

open MeasureTheory

theorem exists_poissonEntrancePath_model_of_markIntensity
    (ν : Measure ℝ) [SigmaFinite ν] (n : ℕ)
    {Jmark : Set ℝ} (hJmark : MeasurableSet Jmark)
    (hJsub : Jmark ⊆ largeJumpBand n)
    (hJpos : 0 < ν Jmark)
    (hbig : ν (largeJumpBand n) < ⊤)
    (lower upper target ρ ε margin : ℝ)
    (hsmall : (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
      ∂((volume : Measure unitInterval).prod
        (ν.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ)
    (hρ : 0 < ρ) (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hJwindow : ∀ x ∈ Jmark, |x - target| < ρ) :
    ∃ (Ωs Ωb : Type) (_ : MeasurableSpace Ωs) (_ : MeasurableSpace Ωb)
      (Ps : Measure Ωs) (Pb : Measure Ωb)
      (Ks : ℕ → Ωs → ℕ)
      (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
      (Kb : ℕ → Ωb → ℕ)
      (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ),
      IsProbabilityMeasure Ps ∧ IsProbabilityMeasure Pb ∧
      IsPoissonPointFamily Ks Xs
        ((volume : Measure unitInterval).prod
          (ν.restrict (smallJumpBand n))) Ps ∧
      IsPoissonPointFamily Kb Xb
        ((volume : Measure unitInterval).prod
          (ν.restrict (largeJumpBand n))) Pb ∧
      0 < (Ps.prod Pb) {ω : Ωs × Ωb |
        (∀ t, lower + (margin - 2 * ρ) ≤
            poissonEntrancePath Ks Xs Kb Xb Set.univ
              (Set.univ ×ˢ largeJumpBand n) t ω ∧
          poissonEntrancePath Ks Xs Kb Xb Set.univ
            (Set.univ ×ˢ largeJumpBand n) t ω ≤
            upper - (margin - 2 * ρ)) ∧
        target - ε < poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) ⊤ ω ∧
        poissonEntrancePath Ks Xs Kb Xb Set.univ
          (Set.univ ×ˢ largeJumpBand n) ⊤ ω < target + ε} := by
  let ms : Measure (unitInterval × ℝ) :=
    (volume : Measure unitInterval).prod (ν.restrict (smallJumpBand n))
  let mb : Measure (unitInterval × ℝ) :=
    (volume : Measure unitInterval).prod (ν.restrict (largeJumpBand n))
  let J : Set (unitInterval × ℝ) := Set.univ ×ˢ Jmark
  let B : Set (unitInterval × ℝ) :=
    Set.univ ×ˢ (largeJumpBand n \ Jmark)
  have hJ : MeasurableSet J := MeasurableSet.univ.prod hJmark
  have hB : MeasurableSet B :=
    MeasurableSet.univ.prod ((measurableSet_largeJumpBand n).diff hJmark)
  have hmb : mb Set.univ < ⊤ := by
    have hmass := unitTime_prod_markWindow
      (ν.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rw [hmass]
    exact hbig
  have hfinJ : mb J < ⊤ :=
    (measure_mono (Set.subset_univ _)).trans_lt hmb
  have hfinB : mb B < ⊤ :=
    (measure_mono (Set.subset_univ _)).trans_lt hmb
  have hJpos' : 0 < mb J := by
    rw [unitTime_prod_restrict_markWindow ν hJmark hJsub]
    exact hJpos
  have hdisj : Disjoint J B := by
    apply Set.disjoint_left.mpr
    intro z hzJ hzB
    exact hzB.2.2 hzJ.2
  have hJwindow' : ∀ z ∈ J, |z.2 - target| < ρ := by
    intro z hz
    exact hJwindow z.2 hz.2
  have hH : J ∪ B = (Set.univ : Set unitInterval) ×ˢ largeJumpBand n :=
    unitTime_target_union_remainder hJsub
  obtain ⟨Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
      hPs, hPb, hds, hdb, hpos⟩ :=
    exists_poissonEntrancePath_model_of_smallMoment
      ms mb hJ hB hfinJ hfinB hJpos' hdisj
      lower upper target ρ ε margin hsmall hρ hε
      hl0 hu0 hly huy hJwindow'
  exact ⟨Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
    hPs, hPb, hds, hdb, by simpa only [hH] using hpos⟩

end ProbabilityTheory
