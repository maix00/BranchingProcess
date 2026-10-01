import Probability.Process.Levy.Jump.Intensity.Cutoff

/-!
# Intensity conditions for a one-jump entrance

A finite truncated first moment and a positive mark window away from zero
produce one cutoff satisfying all quantitative intensity conditions needed
for the independent small/large Poisson model.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- A target window and its remainder partition the finite-activity mark
region when the window lies inside it. -/
theorem unitTime_target_union_remainder
    {A J : Set ℝ} (hJA : J ⊆ A) :
    ((Set.univ : Set unitInterval) ×ˢ J) ∪
      (Set.univ ×ˢ (A \ J)) = Set.univ ×ˢ A := by
  ext z
  constructor
  · rintro (hz | hz)
    · exact ⟨Set.mem_univ _, hJA hz.2⟩
    · exact ⟨Set.mem_univ _, hz.2.1⟩
  · intro hz
    by_cases hj : z.2 ∈ J
    · exact Or.inl ⟨Set.mem_univ _, hj⟩
    · exact Or.inr ⟨Set.mem_univ _, ⟨hz.2, hj⟩⟩

theorem exists_unitTime_cutoff_intensities
    (ν : Measure ℝ) [SigmaFinite ν]
    (hfinite : (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) ≠ ⊤)
    (hlarge : ∀ n, ν (largeJumpBand n) < ⊤)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJpos : 0 < ν J)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hJaway : ∀ x ∈ J, δ ≤ |x|) :
    ∃ n : ℕ,
      (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
        ∂((volume : Measure unitInterval).prod
          (ν.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ ∧
      0 < ((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n))) (Set.univ ×ˢ J) ∧
      ((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n))) Set.univ < ⊤ := by
  obtain ⟨n, hn, hrad⟩ :=
    exists_smallJumpBand_lintegral_lt_and_radius_lt
      ν hfinite ρ δ hρ hδ
  have hJsub : J ⊆ largeJumpBand n := by
    intro x hx
    exact le_trans hrad.le (hJaway x hx)
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [lintegral_unitTime_prod_mark
      (ν.restrict (smallJumpBand n))
      (fun x => ENNReal.ofReal |x|) (by fun_prop)]
    exact hn
  · rw [unitTime_prod_restrict_markWindow ν hJ hJsub]
    exact hJpos
  · have hmass := unitTime_prod_markWindow
      (ν.restrict (largeJumpBand n)) Set.univ
    simp only [Set.univ_prod_univ, Measure.restrict_apply_univ] at hmass
    rw [hmass]
    exact hlarge n

end ProbabilityTheory
