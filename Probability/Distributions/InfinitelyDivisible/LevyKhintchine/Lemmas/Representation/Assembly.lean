/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.Basic
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Integrand
import MeasureTheory.Measure.Levy.JumpRegions
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.ScaledBounds
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.SmallJumpMoment
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.LevyMeasure
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.Drift
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.LargeJumpIdentification
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.SmallJumpIdentification
import all Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Lemmas.Representation.Lemmas.AtomFreeRadii
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Final extraction estimates for the Lévy–Khintchine representation

## Internal proof declarations

* `exists_drift_variance_jumpMeasure_along_seq` selects one sequence along which the drift,
  Gaussian variance, and jump integrals converge simultaneously.
* `psi_eq_levyKhintchine_formula` combines the large-jump and small-jump limits into
  `ψ(ξ) = ibξ - σ²ξ²/2 + ∫ levyCompensatedIntegrand(ξ,x) dν(x)`.
-/

section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-! ### Final assembly of the Lévy-Khintchine triple

The assembly is structured around `exists_drift_variance_jumpMeasure_along_seq`, which
produces all three witnesses `(b, σ², ν)` along a *single* subsequence, via the
canonical-measure (tilted) extraction of ν. The key downstream lemmas are:

* `exists_drift_variance_jumpMeasure_along_seq` — the diagonal extraction.
* `psi_eq_levyKhintchine_formula` — given the diagonal tuple, the formula holds for ψ.
* `psi_decomposition` — packages the tuple + the formula into a `LevyKhintchineTriple`.
-/

/-- **Joint extraction of drift, Gaussian variance, and Lévy measure along a single
subsequence.**

Combines `exists_levyMeasure`, `drift_limit`, and Bolzano-Weierstrass on the scaled
second moment via three nested subsequence extractions. The outer subsequence comes from
the Lévy-measure construction; the drift extracts a sub-subsequence; the variance extracts
a sub-sub-subsequence. All three convergences hold along the final composite subsequence
since `Tendsto` is preserved under further sub-extraction. -/
lemma exists_drift_variance_jumpMeasure_along_seq :
    ∃ (r : ℝ) (b : ℝ) (σ_sq : ℝ≥0) (ν : Measure ℝ), MeasureTheory.IsLevyMeasure ν ∧
      ∃ (t_seq : ℕ → {t : ℝ // 0 < t}),
      r ∈ Set.Ioc (1/2 : ℝ) 1 ∧
      ν {x | |x| = r} = 0 ∧
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 b) ∧
      Tendsto (fun n =>
        (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 (σ_sq : ℝ)) ∧
      (∀ (f : BoundedContinuousFunction ℝ ℝ), (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
        Tendsto (fun n => (t_seq n).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) := by
  -- Step 1: Outer extraction — Lévy measure ν and its witnessing sequence t_seq_ν.
  obtain ⟨ν, hν, t_seq_ν, ht_seq_ν, h_jump_conv⟩ := S.exists_levyMeasure
  -- Step 1b: an atom-free split radius `r ∈ (1/2, 1]`.
  obtain ⟨r, hr_mem, hν_r⟩ :=
    hν.exists_atomFree_radius (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hr_pos : (0 : ℝ) < r := by linarith [hr_mem.1]
  have hr_le1 : r ≤ 1 := hr_mem.2
  have hmeas_ball : MeasurableSet {x : ℝ | |x| < r} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hsubset : {x : ℝ | |x| < r} ⊆ smallJumpSet :=
    fun x hx => mem_smallJumpSet.mpr (lt_of_lt_of_le hx hr_le1)
  -- Step 2: Drift sub-subsequence φ₁ along t_seq_ν, at radius r.
  obtain ⟨b, φ₁, hφ₁_mono, hb⟩ := S.drift_limit hr_pos hr_le1 ht_seq_ν
  -- The composed sequence t_seq_ν ∘ φ₁ still tends to 0.
  have ht_seq₁ : Tendsto (fun n => (t_seq_ν (φ₁ n)).val) atTop (𝓝 0) :=
    ht_seq_ν.comp hφ₁_mono.tendsto_atTop
  -- Step 3: Variance sub-sub-subsequence φ₂ via Bolzano-Weierstrass on Icc 0 C.
  obtain ⟨C, _hC_pos, hC⟩ := S.scaled_second_moment_bounded_along_seq ht_seq₁
  set a : ℕ → ℝ := fun n =>
    (t_seq_ν (φ₁ n)).val⁻¹ *
      ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) with ha_def
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n => by
    have ht_pos : 0 < (t_seq_ν (φ₁ n)).val := (t_seq_ν (φ₁ n)).prop
    refine mul_nonneg (inv_nonneg.mpr ht_pos.le) ?_
    exact setIntegral_nonneg hmeas_ball (fun x _ => sq_nonneg x)
  have ha_bdd : ∀ᶠ n in atTop, a n ∈ Set.Icc (0 : ℝ) C := by
    filter_upwards [hC] with n hCn
    refine ⟨ha_nonneg n, ?_⟩
    -- a n = t⁻¹∫_{|x|<r} x² ≤ t⁻¹∫_small x² ≤ C  (domination over {|x|<r} ⊆ smallJumpSet).
    have ht_pos : 0 < (t_seq_ν (φ₁ n)).val := (t_seq_ν (φ₁ n)).prop
    have hint_sq_small : IntegrableOn (fun x => x ^ 2) smallJumpSet
        (S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) :=
      integrableOn_sq_smallJumpSet _
    have hdom : ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) ≤
        ∫ x in smallJumpSet, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) :=
      setIntegral_mono_set hint_sq_small (ae_of_all _ fun x => sq_nonneg x)
        (LE.le.eventuallyLE hsubset)
    calc a n
        ≤ (t_seq_ν (φ₁ n)).val⁻¹ *
            ∫ x in smallJumpSet, x ^ 2 ∂(S.measure (t_seq_ν (φ₁ n)) : Measure ℝ) :=
          mul_le_mul_of_nonneg_left hdom (inv_nonneg.mpr ht_pos.le)
      _ ≤ C := hCn
  obtain ⟨σ, hσ_mem, φ₂, hφ₂_mono, hσ⟩ :=
    isCompact_Icc.tendsto_subseq' ha_bdd.frequently
  -- Step 4: Assemble the final subsequence t_seq_ν ∘ φ₁ ∘ φ₂.
  set t_seq : ℕ → {t : ℝ // 0 < t} := fun n => t_seq_ν (φ₁ (φ₂ n)) with ht_seq_def
  -- t_seq tends to 0.
  have ht_seq : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) :=
    ht_seq₁.comp hφ₂_mono.tendsto_atTop
  -- Drift convergence along the composite subsequence (at radius r).
  have hb_final : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 b) := hb.comp hφ₂_mono.tendsto_atTop
  -- Variance convergence: σ ≥ 0 so it coerces from Real.toNNReal.
  have hσ_final : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 ((Real.toNNReal σ : ℝ≥0) : ℝ)) := by
    rw [Real.coe_toNNReal σ hσ_mem.1]
    exact hσ
  -- Jump-measure convergence: subseq of jump-convergent is still jump-convergent.
  have h_jump_final : ∀ (f : BoundedContinuousFunction ℝ ℝ),
      (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
      Tendsto (fun n => (t_seq n).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
        atTop (𝓝 (∫ x, f x ∂ν)) := by
    intro f hf
    have h := h_jump_conv f hf
    exact h.comp ((hφ₁_mono.comp hφ₂_mono).tendsto_atTop)
  exact ⟨r, b, Real.toNNReal σ, ν, hν, t_seq, hr_mem, hν_r, ht_seq, hb_final,
    hσ_final, h_jump_final⟩

/-- **ν-side bookkeeping for the LK assembly.** Reorganizes the three subsequential-limit
contributions (drift, compensated small-jump remainder at radius `r`, large-jump integral
over `largeJumpSet r`) into the canonical Lévy-Khintchine triple `(b_r + ∫_{r≤|x|<1} x dν,
σ_sq_r − ∫_{|x|<r} x² dν, ν)`. The key moves are: the small-ball remainder splits off its
own second moment `∫_{|x|<r} x² dν`; the `largeJumpSet r` integral splits into a band
`{r≤|x|<1}` and the `largeJumpSet 1` tail; on the band the uncompensated `exp−1` re-expresses
as the compensated `exp−1−ixξ` plus the drift correction `∫_{r≤|x|<1} x dν`. -/
private lemma psi_levyKhintchine_algebra
    {r : ℝ} (hr : r ∈ Set.Ioc (1/2 : ℝ) 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν) (b_r : ℝ) (σ_sq_r : ℝ≥0) :
    (↑b_r * ↑ξ * I
      + (-(↑(σ_sq_r : ℝ) * ↑ξ ^ 2 / 2)
          + ∫ x in {x | |x| < r},
              (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν))
      + ∫ x in largeJumpSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν =
    ↑(b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν) * ↑ξ * I
      - ↑((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν) * ↑ξ ^ 2 / 2
      + ∫ x, levyCompensatedIntegrand ξ x ∂ν := by
  have hr_pos : (0 : ℝ) < r := by linarith [hr.1]
  have hr1 : r ≤ 1 := hr.2
  -- Abbreviations for the sets.
  set Bball : Set ℝ := {x | |x| < r} with hBball_def
  set Bband : Set ℝ := {x | r ≤ |x| ∧ |x| < 1} with hBband_def
  -- Measurability of the sets.
  have hmeas_ball : MeasurableSet Bball :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hmeas_band : MeasurableSet Bband :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hmeas_ge1 : MeasurableSet (largeJumpSet 1) := measurableSet_largeJumpSet 1
  -- `exp(ixξ)−1` is continuous and globally bounded by 2.
  have hg_cont : Continuous (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) :=
    ((Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const)).sub
      continuous_const)
  have hg_bnd : ∀ x : ℝ, ‖exp ((↑x : ℂ) * ↑ξ * I) - 1‖ ≤ 2 := fun x => by
    rw [show ((↑x : ℂ) * ↑ξ * I) = ((↑(x * ξ) : ℂ)) * I from by push_cast; ring]
    calc ‖exp ((↑(x * ξ) : ℂ) * I) - 1‖
        ≤ ‖exp ((↑(x * ξ) : ℂ) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  -- Finite ν-mass on the band and the outer tail (Lévy measure).
  have hν_band_lt : ν Bband < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx => hx.1)) (hν.measure_setOf_abs_ge_lt_top hr_pos)
  have hν_ge1_lt : ν (largeJumpSet 1) < ⊤ := hν.measure_setOf_abs_ge_lt_top one_pos
  -- `exp(ixξ)−1` is integrable on any set of finite ν-mass (bounded by 2).
  have hexp_int : ∀ s : Set ℝ, ν s < ⊤ →
      IntegrableOn (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1) s ν :=
    fun s hs => Measure.integrableOn_of_bounded hs.ne hg_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hg_bnd)
  -- `ixξ` is integrableOn any finite-mass set contained in {|x|<1} (bounded by |ξ|).
  have hxi_intOn : ∀ s : Set ℝ, MeasurableSet s → s ⊆ {x : ℝ | |x| < 1} → ν s < ⊤ →
      IntegrableOn (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) s ν := by
    intro s hs hsub hfin
    have : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.mpr hfin.ne
    refine (integrable_const (|ξ|)).mono' ?_ ?_
    · exact ((Complex.measurable_ofReal.mul measurable_const).mul
        measurable_const).aestronglyMeasurable
    · refine (ae_restrict_iff' hs).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
      have hx1 : |x| < 1 := hsub hx
      have hnorm : ‖((↑x : ℂ) * ↑ξ * I)‖ = |x| * |ξ| := by
        rw [show ((↑x : ℂ) * ↑ξ * I) = ((↑(x * ξ) : ℂ)) * I from by push_cast; ring,
            norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      rw [hnorm]
      calc |x| * |ξ| ≤ 1 * |ξ| :=
            mul_le_mul_of_nonneg_right (le_of_lt hx1) (abs_nonneg _)
        _ = |ξ| := one_mul _
  -- Set the three opaque ℂ-atoms `A`, `Bcpx`, `Ctail` and two real atoms.
  set A : ℂ := ∫ x in Bball, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν with hA_def
  set Bcpx : ℂ := ∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν with hBcpx_def
  set Ctail : ℂ := ∫ x in largeJumpSet 1, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν with hCtail_def
  set Pball : ℝ := ∫ x in Bball, x ^ 2 ∂ν with hPball_def
  set Pbar : ℝ := ∫ x in Bband, x ∂ν with hPbar_def
  -- Identity 1: remainder split on the ball. The quadratic term is ν-integrable on the ball
  -- via `sq_integrableOn_ball_levy`; the compensated integrand is the cubic Taylor remainder
  -- minus the quadratic term (both ν-integrable on the ball for a Lévy measure).
  have hquad_ball : IntegrableOn (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) Bball ν := by
    have hrw : (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) =
        fun x : ℝ => (↑((x ^ 2 * (ξ ^ 2 / 2) : ℝ)) : ℂ) := by
      funext x; push_cast; ring
    rw [hrw]
    exact ((sq_integrableOn_ball_levy hν r).mul_const (ξ ^ 2 / 2)).ofReal
  have hcomp_ball : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) Bball ν := by
    -- On `{|x| < r} ⊆ {|x| < 1}` the compensated integrand's indicator fires, so it equals
    -- `exp(ixξ) − 1 − ixξ`; integrability transfers from the global compensated integrand.
    refine ((integrable_levyCompensatedIntegrand hν ξ).integrableOn).congr ?_
    filter_upwards [ae_restrict_mem hmeas_ball] with x hx
    have hx1 : |x| < 1 := lt_of_lt_of_le hx hr1
    simp [levyCompensatedIntegrand, hx1]
  have h_id1 : (∫ x in Bball,
      (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)
      = A + (↑Pball : ℂ) * ↑ξ ^ 2 / 2 := by
    rw [integral_add hcomp_ball hquad_ball, hA_def]
    congr 1
    -- The quadratic ν-integral over the ball: pull `↑ξ²/2` out and recognize `∫ x²`.
    have hquad_eq : ∀ x : ℝ, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 = (↑ξ ^ 2 / 2 : ℂ) * (↑(x ^ 2) : ℂ) := by
      intro x; push_cast; ring
    calc (∫ x in Bball, ((↑x : ℂ) * ↑ξ) ^ 2 / 2 ∂ν)
        = ∫ x in Bball, (↑ξ ^ 2 / 2 : ℂ) * (↑(x ^ 2) : ℂ) ∂ν :=
          setIntegral_congr_fun hmeas_ball (fun x _ => hquad_eq x)
      _ = (↑ξ ^ 2 / 2 : ℂ) * ∫ x in Bball, (↑(x ^ 2) : ℂ) ∂ν := integral_const_mul _ _
      _ = (↑ξ ^ 2 / 2 : ℂ) * (↑Pball : ℂ) := by
          rw [hPball_def]; congr 1; exact integral_complex_ofReal
      _ = (↑Pball : ℂ) * ↑ξ ^ 2 / 2 := by ring
  -- Identity 2: largeJumpSet r splits into band ⊎ largeJumpSet 1.
  have h_id2 : (∫ x in largeJumpSet r, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)
      = (∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν) + Ctail := by
    have h_disj : Disjoint Bband (largeJumpSet 1) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd (mem_largeJumpSet.mp hx') (not_le.mpr hx.2)
    have h_union : largeJumpSet r = Bband ∪ largeJumpSet 1 := by
      ext x
      simp only [largeJumpSet, hBband_def, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · intro hx
        rcases lt_or_ge (|x|) 1 with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
      · rintro (⟨h, _⟩ | h)
        · exact h
        · exact le_trans hr1 h
    rw [hCtail_def, h_union,
      setIntegral_union h_disj hmeas_ge1 (hexp_int Bband hν_band_lt)
        (hexp_int (largeJumpSet 1) hν_ge1_lt)]
  -- Identity 3: band uncompensated = compensated + drift correction.
  have hband_sub : Bband ⊆ {x : ℝ | |x| < 1} := fun x hx => hx.2
  have hxi_band : IntegrableOn (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) Bband ν :=
    hxi_intOn Bband hmeas_band hband_sub hν_band_lt
  have hcomp_band : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) Bband ν :=
    (hexp_int Bband hν_band_lt).sub hxi_band
  have h_id3 : (∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)
      = Bcpx + (↑Pbar : ℂ) * ↑ξ * I := by
    have hsplit : (∫ x in Bband, (exp ((↑x : ℂ) * ↑ξ * I) - 1) ∂ν)
        = Bcpx + ∫ x in Bband, ((↑x : ℂ) * ↑ξ * I) ∂ν := by
      rw [hBcpx_def, ← integral_add hcomp_band hxi_band]
      exact setIntegral_congr_fun hmeas_band (fun x _ => by ring)
    rw [hsplit]
    congr 1
    -- The band drift integral: pull `↑ξ·I` out and recognize `∫ x`.
    calc (∫ x in Bband, ((↑x : ℂ) * ↑ξ * I) ∂ν)
        = ∫ x in Bband, ((↑ξ * I : ℂ) * (↑x : ℂ)) ∂ν :=
          setIntegral_congr_fun hmeas_band (fun x _ => by ring)
      _ = (↑ξ * I : ℂ) * ∫ x in Bband, (↑x : ℂ) ∂ν := integral_const_mul _ _
      _ = (↑ξ * I : ℂ) * (↑Pbar : ℂ) := by rw [hPbar_def]; congr 1; exact integral_complex_ofReal
      _ = (↑Pbar : ℂ) * ↑ξ * I := by ring
  -- Identity 4: global compensated split.
  have h_levy_int : Integrable (levyCompensatedIntegrand ξ) ν :=
    integrable_levyCompensatedIntegrand hν ξ
  -- `levyComp = exp−1−ixξ` on `{|x|<1}` and `= exp−1` on `largeJumpSet 1`.
  have hlevy_small : ∀ x : ℝ, |x| < 1 →
      levyCompensatedIntegrand ξ x = exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I := by
    intro x hx
    simp only [levyCompensatedIntegrand_def, ite_eq_left hx, mul_one]
  have hlevy_large : ∀ x : ℝ, x ∈ largeJumpSet 1 →
      levyCompensatedIntegrand ξ x = exp ((↑x : ℂ) * ↑ξ * I) - 1 :=
    fun x hx => levyCompensatedIntegrand_eq_exp_sub_one_of_one_le_abs (mem_largeJumpSet.mp hx)
  have h_id4 : (∫ x, levyCompensatedIntegrand ξ x ∂ν) = A + Bcpx + Ctail := by
    -- Split ℝ = smallJumpSet ⊎ largeJumpSet 1.
    have hsplit_top : (∫ x, levyCompensatedIntegrand ξ x ∂ν)
        = (∫ x in smallJumpSet, levyCompensatedIntegrand ξ x ∂ν)
          + ∫ x in (smallJumpSet)ᶜ, levyCompensatedIntegrand ξ x ∂ν :=
      (integral_add_compl measurableSet_smallJumpSet h_levy_int).symm
    have hcompl_small : (smallJumpSet : Set ℝ)ᶜ = largeJumpSet 1 := by
      rw [smallJumpSet_eq_compl_largeJumpSet_one, compl_compl]
    -- On largeJumpSet 1, levyComp = exp−1, giving Ctail.
    have h_large_eq : (∫ x in (smallJumpSet)ᶜ, levyCompensatedIntegrand ξ x ∂ν) = Ctail := by
      rw [hcompl_small, hCtail_def]
      exact setIntegral_congr_fun hmeas_ge1 (fun x hx => hlevy_large x hx)
    -- On smallJumpSet, levyComp = exp−1−ixξ; split into Bball ⊎ Bband.
    have h_small_eq : (∫ x in smallJumpSet, levyCompensatedIntegrand ξ x ∂ν) = A + Bcpx := by
      have h_disj : Disjoint Bball Bband := by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx'.1 (not_le.mpr hx)
      have h_union : (smallJumpSet : Set ℝ) = Bball ∪ Bband := by
        ext x
        simp only [mem_smallJumpSet, hBball_def, hBband_def, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro hx
          rcases lt_or_ge (|x|) r with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h, hx⟩
        · rintro (h | ⟨_, h⟩)
          · exact lt_of_lt_of_le h hr1
          · exact h
      -- Rewrite levyComp to exp−1−ixξ on smallJumpSet, then split.
      have hrw : (∫ x in smallJumpSet, levyCompensatedIntegrand ξ x ∂ν)
          = ∫ x in smallJumpSet, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I) ∂ν :=
        setIntegral_congr_fun measurableSet_smallJumpSet
          (fun x hx => hlevy_small x (mem_smallJumpSet.mp hx))
      rw [hrw, h_union,
        setIntegral_union h_disj hmeas_band hcomp_ball hcomp_band, hA_def, hBcpx_def]
    rw [hsplit_top, h_large_eq, h_small_eq]
  rw [h_id1, h_id2, h_id3, h_id4]
  push_cast
  ring

/-- **The Lévy-Khintchine formula for ψ.** Given the drift `b`, the Gaussian variance
`σ²`, and an externally-provided Lévy measure `ν` on `ℝ\{0}` (σ-finite with
`∫ min(1, x²) dν < ∞`, atom-free at the split radius `r`),
together with the three subsequential limits from
`exists_drift_variance_jumpMeasure_along_seq`, the exponent `ψ` admits the canonical
Lévy-Khintchine decomposition.

The hypotheses encode exactly the output of the diagonal extraction:
* `hb` — drift convergence,
* `hσ` — second-moment convergence,
* `h_jump` — vague (vanishing-near-0) convergence of `t⁻¹·μ_t` to `ν`.

**Soundness note (2026-06):** the formula is stated at an extracted *atom-free* split
radius `r ∈ (1/2, 1]`. The drift `b_r` and Gaussian-variance `σ_sq_r` are the radius-`r`
subsequential limits; the standard radius-1 compensator is recovered by converting at
the ν level — the drift correction `∫_{r≤|x|<1} x dν` and the variance correction
`−∫_{|x|<r} x² dν` (which removes the small-jump second moment the compensated integral
already carries). An earlier radius-1 statement was *false* (it double-counted the
small-jump second moment, e.g. for compound Poisson `ν = δ_{1/2}`).

**Proof strategy:**
Combine the four limit identifications in `𝓝 (S.exponent ξ)` at split radius `r`:
1. `charFun_scaled_limit`: `t⁻¹·(charFun(μ_t)(ξ) − 1) → ψ(ξ)`.
2. `drift_term`: `iξ·(t⁻¹·∫_{|x|<r} x dμ_t) → b_r·ξ·I`.
3. `scaled_smallBall_compensated_tendsto`: the small-jump identification at radius `r`.
4. `scaled_largeJumpSet_charFun_tendsto`: the large-jump identification at radius `r`.
The per-`t` identity `charFun_sub_one_div_decomp` lets `tendsto_nhds_unique` equate the
two limits; `psi_levyKhintchine_algebra` then reorganizes the ν-side integrals into the
canonical triple. -/
lemma psi_eq_levyKhintchine_formula
    {r : ℝ} (hr : r ∈ Set.Ioc (1/2 : ℝ) 1)
    (b_r : ℝ) (σ_sq_r : ℝ≥0) {ν : Measure ℝ} (hν : MeasureTheory.IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (ht_seq : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0))
    (hb : Tendsto (fun n =>
        (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
        atTop (𝓝 b_r))
    (hσ : Tendsto (fun n =>
        (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq n) : Measure ℝ))
        atTop (𝓝 ((σ_sq_r : ℝ≥0) : ℝ)))
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
        Tendsto (fun n => (t_seq n).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq n) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν)))
    (ξ : ℝ) :
    S.exponent ξ =
      ↑(b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν) * ↑ξ * I
      - ↑((σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν) * ↑ξ ^ 2 / 2
      + ∫ x, levyCompensatedIntegrand ξ x ∂ν := by
  have hr_pos : (0 : ℝ) < r := by linarith [hr.1]
  -- B1: pull `t_seq` back through the comap filter and obtain the LHS limit.
  have htseq_filter : Tendsto t_seq atTop (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) := by
    rw [Filter.tendsto_comap_iff]
    exact tendsto_nhdsWithin_iff.mpr
      ⟨ht_seq, Filter.Eventually.of_forall (fun n => (t_seq n).prop)⟩
  have hLHS : Tendsto (fun n =>
      (charFun (S.measure (t_seq n) : Measure ℝ) ξ - 1) / (↑(t_seq n).val : ℂ))
      atTop (𝓝 (S.exponent ξ)) :=
    (S.charFun_scaled_limit ξ).comp htseq_filter
  -- B3: the three term-limits (types inferred from the respective lemmas).
  have hT1 := S.drift_term ξ ht_seq hb
  have hT2 := S.scaled_smallBall_compensated_tendsto hr_pos hr.2 ξ
    hν hν_r hσ h_jump
  have hT3 := S.scaled_largeJumpSet_charFun_tendsto hr_pos ξ
    hν hν_r h_jump
  -- B4: sum of the three limits (matching the per-`n` decomposition pointwise).
  have hRHS_lim := (hT1.add hT2).add hT3
  -- B2 + B5: the LHS quotient equals the per-`n` sum; uniqueness of limits.
  -- The decomposition emits `↑(t⁻¹)`; the limit lemmas emit `(↑t)⁻¹`; bridge via `ofReal_inv`.
  have hLHS_sum := hLHS.congr (fun n => by
    rw [S.charFun_sub_one_div_decomp (t_seq n) ξ hr.2, Complex.ofReal_inv])
  have h_eq := tendsto_nhds_unique hLHS_sum hRHS_lim
  rw [h_eq]
  -- B6: ν-side algebra (handled by the dedicated identity lemma above).
  exact psi_levyKhintchine_algebra hr ξ hν b_r σ_sq_r

end ConvolutionSemigroup

end ProbabilityTheory
