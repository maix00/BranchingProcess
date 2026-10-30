/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.Levy.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Defs
import MeasureTheory.Integral.Lebesgue.RestrictLimit

/-!
# Truncation regions and the canonical Lévy cutoff

The canonical unit truncation is the displacement
`h(x) = x` for `|x| < 1` and `h(x) = 0` otherwise. Under the finite-variation
condition `∫_{|x|≤1} |x| dν < ∞`, this displacement is integrable. We also use
the reciprocal bands `smallJumpBand n` and `largeJumpBand n` to split a Lévy
measure away from its null atom at zero and to select small-variation cutoffs.

The map `x ↦ x 1_{|x|<1}` is the canonical truncation function in
Baurdoux and Papapantoleon, *An Introduction to Lévy Processes*, lecture notes
(February 6, 2015), §5, Definition 5.6 and Example 5.9(i). The closed-ball
convention in Sato, *Lévy Processes and Infinitely Divisible Distributions*,
Theorem 8.1, differs only at the unit boundary and adjusts the drift parameter.

## Public declarations

* `smallJumpDisplacement x` is `x` when `|x| < 1` and `0` otherwise;
  `integrable_smallJumpDisplacement` proves its integrability from
  `IntegrableOn id {x | |x| ≤ 1} ν`.
* `smallJumpBand n = {x | 0 < |x| ∧ |x| < 1/(n+1)}` and
  `largeJumpBand n = {x | 1/(n+1) ≤ |x|}`; the bands are disjoint, measurable,
  and their union is `{x | x ≠ 0}`.
* `IsLevyMeasure.measure_largeJumpBand_lt_top` gives finite mass to every
  reciprocal large-jump band.
* `IsLevyMeasure.restrict_smallJumpBand_add_restrict_largeJumpBand` and
  `IsLevyMeasure.integral_smallJumpBand_add_largeJumpBand` split a Lévy measure
  and each integrable observable over these two bands.
* `eventually_not_mem_smallJumpBand` and
  `lintegral_smallJumpBand_abs_eq_min` give the cutoff limit and the identity
  between the absolute-jump and `min(1, |x|)` integrals.
* `exists_smallJumpBand_lintegral_lt` and
  `exists_smallJumpBand_lintegral_lt_and_radius_lt` choose a cutoff with small
  first-moment mass, optionally with a prescribed upper bound on its radius.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter Set

/-- Nonzero jumps smaller than a reciprocal natural cutoff. -/
def smallJumpBand (n : ℕ) : Set ℝ :=
  {x | 0 < |x| ∧ |x| < 1 / ((n : ℝ) + 1)}

/-- Jumps at or above the same reciprocal cutoff. -/
def largeJumpBand (n : ℕ) : Set ℝ :=
  {x | 1 / ((n : ℝ) + 1) ≤ |x|}

/-- The displacement retained by the canonical radius-one truncation:
`x` for `|x| < 1` and `0` elsewhere. -/
noncomputable def smallJumpDisplacement (x : ℝ) : ℝ :=
  if |x| < 1 then x else 0

/-- The canonical small-jump displacement is integrable whenever the first
absolute moment is finite on the unit ball. -/
theorem integrable_smallJumpDisplacement {ν : Measure ℝ}
    (h : IntegrableOn (fun x : ℝ => x) {x : ℝ | |x| ≤ 1} ν) :
    Integrable smallJumpDisplacement ν := by
  have hsub : Ioo (-1 : ℝ) 1 ⊆ {x : ℝ | |x| ≤ 1} := by
    intro x hx
    simp only [mem_Ioo, mem_ofPred_eq] at hx ⊢
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hint := h.mono_set hsub
  have hs : MeasurableSet (Ioo (-1 : ℝ) 1) := measurableSet_Ioo
  have heq : smallJumpDisplacement = (Ioo (-1 : ℝ) 1).indicator id := by
    funext x
    by_cases hx : |x| < 1
    · have hmem : x ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hx
      simp [smallJumpDisplacement, hx, Set.indicator_of_mem hmem]
    · have hmem : x ∉ Ioo (-1 : ℝ) 1 := by simpa [abs_lt] using hx
      simp [smallJumpDisplacement, hx, Set.indicator_of_notMem hmem]
  rw [heq]
  exact hint.integrable_indicator hs

theorem smallJumpBand_union_largeJumpBand (n : ℕ) :
    smallJumpBand n ∪ largeJumpBand n = {x : ℝ | x ≠ 0} := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact abs_pos.mp hx.1
    · have hr : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact abs_pos.mp (hr.trans_le hx)
  · intro hx
    have hpos : 0 < |x| := abs_pos.mpr hx
    by_cases hlt : |x| < 1 / ((n : ℝ) + 1)
    · exact Or.inl ⟨hpos, hlt⟩
    · exact Or.inr (le_of_not_gt hlt)

theorem disjoint_smallJumpBand_largeJumpBand (n : ℕ) :
    Disjoint (smallJumpBand n) (largeJumpBand n) := by
  apply Set.disjoint_left.mpr
  intro x hsmall hlarge
  exact (not_lt_of_ge hlarge) hsmall.2

theorem measurableSet_smallJumpBand (n : ℕ) : MeasurableSet (smallJumpBand n) := by
  unfold smallJumpBand
  have habs : Measurable (fun x : ℝ => |x|) := by fun_prop
  exact (measurableSet_lt (measurable_const : Measurable fun _ : ℝ => (0 : ℝ)) habs).inter
    (measurableSet_lt habs measurable_const)

theorem measurableSet_largeJumpBand (n : ℕ) : MeasurableSet (largeJumpBand n) := by
  unfold largeJumpBand
  have habs : Measurable (fun x : ℝ => |x|) := by fun_prop
  exact measurableSet_le measurable_const habs

/-- A Lévy measure has finite mass on every reciprocal large-jump band. -/
theorem _root_.MeasureTheory.IsLevyMeasure.measure_largeJumpBand_lt_top
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (n : ℕ) :
    ν (largeJumpBand n) < ⊤ := by
  have hcut : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  exact hν.measure_setOf_abs_ge_lt_top hcut

/-- For a Lévy measure the small and large restrictions exhaust its
intensity: the only omitted mark is zero, which has zero mass. -/
theorem _root_.MeasureTheory.IsLevyMeasure.restrict_smallJumpBand_add_restrict_largeJumpBand
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (n : ℕ) :
    ν.restrict (smallJumpBand n) + ν.restrict (largeJumpBand n) = ν := by
  rw [← Measure.restrict_union (disjoint_smallJumpBand_largeJumpBand n)
    (measurableSet_largeJumpBand n), smallJumpBand_union_largeJumpBand]
  have hcomp : ({x : ℝ | x ≠ 0} : Set ℝ)ᶜ = {0} := by
    ext x
    simp
  have h := Measure.restrict_add_restrict_compl
    (show MeasurableSet {x : ℝ | x ≠ 0} from (measurableSet_singleton (x := (0 : ℝ))).compl)
    (μ := ν)
  rw [hcomp, Measure.restrict_zero_set hν.zero_singleton, add_zero] at h
  exact h

/-- Any integrable jump observable splits into its small and large mark
contributions at a fixed cutoff. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_smallJumpBand_add_largeJumpBand
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f ν) :
    (∫ x in smallJumpBand n, f x ∂ν) +
      (∫ x in largeJumpBand n, f x ∂ν) = ∫ x, f x ∂ν := by
  have hs : Integrable f (ν.restrict (smallJumpBand n)) :=
    hf.mono_measure Measure.restrict_le_self
  have hl : Integrable f (ν.restrict (largeJumpBand n)) :=
    hf.mono_measure Measure.restrict_le_self
  rw [← integral_add_measure hs hl, hν.restrict_smallJumpBand_add_restrict_largeJumpBand]

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
  obtain ⟨n, hn⟩ := MeasureTheory.exists_lintegral_restrict_lt_of_eventually_not_mem
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
  have hlim := MeasureTheory.tendsto_lintegral_restrict_of_eventually_not_mem
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
