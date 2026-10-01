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

/-- The finite-variation condition selects a cutoff and constructs a complete
small-plus-large jump path with a positive entrance event. -/
theorem exists_poissonEntrancePath_model_of_finiteVariation
    (ν : Measure ℝ) [SigmaFinite ν]
    (hfinite : (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) ≠ ⊤)
    (hlarge : ∀ n, ν (largeJumpBand n) < ⊤)
    {Jmark : Set ℝ} (hJmark : MeasurableSet Jmark)
    (hJpos : 0 < ν Jmark)
    (lower upper target ρ ε margin δ : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hJwindow : ∀ x ∈ Jmark, |x - target| < ρ)
    (hJaway : ∀ x ∈ Jmark, δ ≤ |x|) :
    ∃ (n : ℕ) (Ωs Ωb : Type)
      (_ : MeasurableSpace Ωs) (_ : MeasurableSpace Ωb)
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
  obtain ⟨n, hn, hrad⟩ :=
    exists_smallJumpBand_lintegral_lt_and_radius_lt
      ν hfinite ρ δ hρ hδ
  have hsub : Jmark ⊆ largeJumpBand n := by
    intro x hx
    exact le_trans hrad.le (hJaway x hx)
  have hsmall : (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
      ∂((volume : Measure unitInterval).prod
        (ν.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ := by
    rw [lintegral_unitTime_prod_mark
      (ν.restrict (smallJumpBand n))
      (fun x => ENNReal.ofReal |x|) (by fun_prop)]
    exact hn
  obtain ⟨Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
      hPs, hPb, hds, hdb, hpos⟩ :=
    exists_poissonEntrancePath_model_of_markIntensity
      ν n hJmark hsub hJpos (hlarge n)
      lower upper target ρ ε margin hsmall hρ hε
      hl0 hu0 hly huy hJwindow
  exact ⟨n, Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
    hPs, hPb, hds, hdb, hpos⟩

end ProbabilityTheory
