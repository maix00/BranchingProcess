import Probability.Distributions.Stable.Sign
import Probability.Distributions.Stable.LevyMeasure.EndpointLaw
import Probability.Process.Levy.Jump.PoissonConfiguration.Entrance
import Probability.Distributions.Stable.LevyMeasure.Tails
import Probability.Distributions.Stable.LevyMeasure.Windows
import Probability.Distributions.Stable.LevyMeasure.EntranceWindows

/-!
# Signs of jumps in a two-sided stable law

The sign condition on the one-step distribution forces the uncompensated
Lévy measure to charge both open half-lines when the index is below one.
-/

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem IsStrictlyAlphaStable.twoSidedLevyMass_of_cdfAtZero_of_model
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
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
    0 < T.levyMeasure (Set.Iio 0) ∧
      0 < T.levyMeasure (Set.Ioi 0) := by
  have hμ := h.twoSidedMass_of_cdfAtZero hcdf
  have hsfirst := h.integrable_unitTime_smallJumpMark T hT hα n
  have hlaw := h.law_unitTime_split_poissonRandomMeasures T hT hα n hds hdb
  constructor
  · by_contra hn
    have hνneg : T.levyMeasure (Set.Iio 0) = 0 :=
      nonpos_iff_eq_zero.mp (le_of_not_gt hn)
    have hzero := measure_Iio_zero_of_split_poisson_law_no_negative_intensity
      n hds hdb hsfirst (T.levyMeasure_largeJumpBand_lt_top n) hlaw hνneg
    exact hμ.1.ne' hzero
  · by_contra hn
    have hνpos : T.levyMeasure (Set.Ioi 0) = 0 :=
      nonpos_iff_eq_zero.mp (le_of_not_gt hn)
    have hzero := measure_Ioi_zero_of_split_poisson_law_no_positive_intensity
      n hds hdb hsfirst (T.levyMeasure_largeJumpBand_lt_top n) hlaw hνpos
    exact hμ.2.ne' hzero

/-- The CDF condition implies genuine jumps of both signs; the canonical
Poisson pair used in the proof exists without any target-window premise. -/
theorem IsStrictlyAlphaStable.twoSidedLevyMass_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < T.levyMeasure (Set.Iio 0) ∧
      0 < T.levyMeasure (Set.Ioi 0) := by
  letI : SigmaFinite T.levyMeasure := T.levyMeasure_isLevyMeasure.sigmaFinite
  let ms : Measure (unitInterval × ℝ) :=
    (volume : Measure unitInterval).prod
      (T.levyMeasure.restrict (smallJumpBand 0))
  let mb : Measure (unitInterval × ℝ) :=
    (volume : Measure unitInterval).prod
      (T.levyMeasure.restrict (largeJumpBand 0))
  letI : SigmaFinite ms := by infer_instance
  letI : SigmaFinite mb := by infer_instance
  obtain ⟨Ωs, mΩs, Ps, Ks, Xs, hPs, hds⟩ := exists_isPoissonPointFamily ms
  obtain ⟨Ωb, mΩb, Pb, Kb, Xb, hPb, hdb⟩ := exists_isPoissonPointFamily mb
  letI := mΩs
  letI := mΩb
  letI := hPs
  letI := hPb
  exact h.twoSidedLevyMass_of_cdfAtZero_of_model
    T hT hα hcdf 0 hds hdb

/-- Under homogeneity, mass anywhere on the positive half-line already
forces positive mass beyond the unit threshold. -/
theorem IsStrictlyAlphaStable.levyMeasure_Ioi_one_pos_of_Ioi_zero_pos
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hpos : 0 < T.levyMeasure (Set.Ioi 0)) :
    0 < T.levyMeasure (Set.Ioi 1) := by
  by_contra hn
  have hzero : T.levyMeasure (Set.Ioi 1) = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hn)
  have hcover : (Set.Ioi (0 : ℝ)) =
      ⋃ n : ℕ, Set.Ioi (1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro hx
      have he : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < x :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hx)
      obtain ⟨n, hn⟩ := he.exists
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      exact lt_trans (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hn
  have hnull : T.levyMeasure (Set.Ioi 0) = 0 := by
    rw [hcover]
    apply measure_iUnion_null
    intro n
    rw [h.levyMeasure_Ioi T hT (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
    simp [hzero]
  exact hpos.ne' hnull

/-- The symmetric negative-tail consequence of homogeneity. -/
theorem IsStrictlyAlphaStable.levyMeasure_Iio_neg_one_pos_of_Iio_zero_pos
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hneg : 0 < T.levyMeasure (Set.Iio 0)) :
    0 < T.levyMeasure (Set.Iio (-1)) := by
  by_contra hn
  have hzero : T.levyMeasure (Set.Iio (-1)) = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hn)
  have hcover : (Set.Iio (0 : ℝ)) =
      ⋃ n : ℕ, Set.Iio (-(1 / ((n : ℝ) + 1))) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion]
    constructor
    · intro hx
      have he : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < -x :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const (by linarith))
      obtain ⟨n, hn⟩ := he.exists
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hnull : T.levyMeasure (Set.Iio 0) = 0 := by
    rw [hcover]
    apply measure_iUnion_null
    intro n
    rw [h.levyMeasure_Iio_neg T hT (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
    simp [hzero]
  exact hneg.ne' hnull

/-- The original sign hypothesis gives positive unit tails on both sides
of the stable Lévy measure. -/
theorem IsStrictlyAlphaStable.twoSidedLevyUnitTails_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < T.levyMeasure (Set.Iio (-1)) ∧
      0 < T.levyMeasure (Set.Ioi 1) := by
  obtain ⟨hneg, hpos⟩ := h.twoSidedLevyMass_of_cdfAtZero T hT hα hcdf
  exact ⟨h.levyMeasure_Iio_neg_one_pos_of_Iio_zero_pos T hT hneg,
    h.levyMeasure_Ioi_one_pos_of_Ioi_zero_pos T hT hpos⟩

/-- Both bounded jump windows needed for the one-jump entrance have
positive intensity, with no window positivity added as an assumption. -/
theorem IsStrictlyAlphaStable.twoSidedLevyWindows_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hα : α < 1) (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    0 < T.levyMeasure (Set.Ioo (-R) (-r)) ∧
      0 < T.levyMeasure (Set.Ioo r R) := by
  obtain ⟨hneg, hpos⟩ := h.twoSidedLevyUnitTails_of_cdfAtZero T hT hα hcdf
  exact ⟨h.levyMeasure_neg_Ioo_pos_of_neg_tail T hT h.1 hr hrR hneg,
    h.levyMeasure_Ioo_pos_of_pos_tail T hT h.1 hr hrR hpos⟩

/-- The original CDF condition supplies a positive-jump entrance window
after a cutoff controlling the remaining small-jump variation. -/
theorem IsStrictlyAlphaStable.exists_positiveWindow_cutoff_intensities_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hαlt : α < 1) (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hδr : δ ≤ r) :
    ∃ n : ℕ,
      (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
        ∂((volume : Measure unitInterval).prod
          (T.levyMeasure.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ ∧
      0 < ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n)))
          (Set.univ ×ˢ Set.Ioo r R) ∧
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Set.univ < ⊤ := by
  have htail := (h.twoSidedLevyUnitTails_of_cdfAtZero T hT hαlt hcdf).2
  exact h.exists_positiveWindow_cutoff_intensities T hT h.1 hαlt htail
    hr hrR ρ δ hρ hδ hδr

/-- The corresponding negative-jump cutoff also needs only the original
CDF condition. -/
theorem IsStrictlyAlphaStable.exists_negativeWindow_cutoff_intensities_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (T : LevyKhintchineTriple)
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
    (hαlt : α < 1) (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hδr : δ ≤ r) :
    ∃ n : ℕ,
      (∫⁻ z : unitInterval × ℝ, ENNReal.ofReal |z.2|
        ∂((volume : Measure unitInterval).prod
          (T.levyMeasure.restrict (smallJumpBand n)))) < ENNReal.ofReal ρ ∧
      0 < ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n)))
          (Set.univ ×ˢ Set.Ioo (-R) (-r)) ∧
      ((volume : Measure unitInterval).prod
        (T.levyMeasure.restrict (largeJumpBand n))) Set.univ < ⊤ := by
  have htail := (h.twoSidedLevyUnitTails_of_cdfAtZero T hT hαlt hcdf).1
  exact h.exists_negativeWindow_cutoff_intensities T hT h.1 hαlt htail
    hr hrR ρ δ hρ hδ hδr

end ProbabilityTheory
