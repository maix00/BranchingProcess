import Probability.Process.Levy.Jump.Intensity.TimeMark
import Probability.Process.Levy.Jump.VariationLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A deterministic small-jump cutoff

Finite truncated first moment gives a cutoff below which the expected total
absolute jump size is arbitrarily small. The bands exclude zero explicitly,
so this result does not need a separate no-atom-at-zero hypothesis.
-/

namespace ProbabilityTheory

open MeasureTheory Filter

/-- Nonzero jumps smaller than a reciprocal natural cutoff. -/
def smallJumpBand (n : ℕ) : Set ℝ :=
  {x | 0 < |x| ∧ |x| < 1 / ((n : ℝ) + 1)}

/-- Jumps at or above the same reciprocal cutoff. -/
def largeJumpBand (n : ℕ) : Set ℝ :=
  {x | 1 / ((n : ℝ) + 1) ≤ |x|}

theorem measurableSet_smallJumpBand (n : ℕ) : MeasurableSet (smallJumpBand n) := by
  unfold smallJumpBand
  have habs : Measurable (fun x : ℝ => |x|) := by fun_prop
  exact (measurableSet_lt (measurable_const : Measurable fun _ : ℝ => (0 : ℝ)) habs).inter
    (measurableSet_lt habs measurable_const)

theorem measurableSet_largeJumpBand (n : ℕ) : MeasurableSet (largeJumpBand n) := by
  unfold largeJumpBand
  have habs : Measurable (fun x : ℝ => |x|) := by fun_prop
  exact measurableSet_le measurable_const habs

theorem eventually_not_mem_smallJumpBand (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, x ∉ smallJumpBand n := by
  by_cases hx : x = 0
  · apply Filter.Eventually.of_forall
    intro n
    simp [smallJumpBand, hx]
  · have hpos : 0 < |x| := abs_pos.mpr hx
    filter_upwards
      [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hpos]
      with n hn
    intro hmem
    exact (lt_asymm hmem.2 hn)

theorem lintegral_smallJumpBand_abs_eq_min (ν : Measure ℝ) (n : ℕ) :
    (∫⁻ x in smallJumpBand n, ENNReal.ofReal |x| ∂ν) =
      ∫⁻ x in smallJumpBand n, ENNReal.ofReal (min 1 |x|) ∂ν := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_smallJumpBand n)] with x hx
  have hden : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hx1 : |x| ≤ 1 := (le_of_lt hx.2).trans hden
  rw [min_eq_right hx1]

/-- Under the standard finite-variation first-moment condition, a small
enough fixed cutoff has arbitrarily small absolute-jump intensity. -/
theorem exists_smallJumpBand_lintegral_lt
    (ν : Measure ℝ)
    (hfinite : (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) ≠ ⊤)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n : ℕ,
      (∫⁻ x in smallJumpBand n, ENNReal.ofReal |x| ∂ν) <
        ENNReal.ofReal ρ := by
  obtain ⟨n, hn⟩ := exists_lintegral_restrict_lt_of_eventually_not_mem
    ν (fun x => ENNReal.ofReal (min 1 |x|)) smallJumpBand
    (by fun_prop) measurableSet_smallJumpBand hfinite
    (Filter.Eventually.of_forall eventually_not_mem_smallJumpBand)
    ρ hρ
  refine ⟨n, ?_⟩
  rw [lintegral_smallJumpBand_abs_eq_min]
  exact hn

/-- The cutoff can be made small in both expected variation and spatial
radius, using the same deterministic index. -/
theorem exists_smallJumpBand_lintegral_lt_and_radius_lt
    (ν : Measure ℝ)
    (hfinite : (∫⁻ x, ENNReal.ofReal (min 1 |x|) ∂ν) ≠ ⊤)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ n : ℕ,
      (∫⁻ x in smallJumpBand n, ENNReal.ofReal |x| ∂ν) <
        ENNReal.ofReal ρ ∧
      1 / ((n : ℝ) + 1) < δ := by
  have hlim := tendsto_lintegral_restrict_of_eventually_not_mem
    ν (fun x => ENNReal.ofReal (min 1 |x|)) smallJumpBand
    (by fun_prop) measurableSet_smallJumpBand hfinite
    (Filter.Eventually.of_forall eventually_not_mem_smallJumpBand)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (∫⁻ x in smallJumpBand n,
        ENNReal.ofReal (min 1 |x|) ∂ν) < ENNReal.ofReal ρ :=
    hlim.eventually_lt_const (ENNReal.ofReal_pos.mpr hρ)
  have hradius : ∀ᶠ n : ℕ in atTop,
      1 / ((n : ℝ) + 1) < δ :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hδ
  obtain ⟨n, hn, hrad⟩ := (hsmall.and hradius).exists
  exact ⟨n, by rwa [lintegral_smallJumpBand_abs_eq_min], hrad⟩

end ProbabilityTheory
