/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Probability.Process.Stable.Levy
public import Probability.Process.Path.Skorokhod.RationalTime

/-!
# Fixed-time continuity of stable Lévy processes

Stable scaling makes increments over intervals whose lengths tend to zero
converge in distribution to zero.  Combined with càdlàg sample paths, this
shows that there is almost surely no jump at any fixed positive time.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]

-- The local probability-law instance is needed by Mathlib's distribution
-- convergence structure and is derived from the stable increment law.
set_option linter.style.haveILetI false in
/-- A stable Lévy process has no jump at a fixed positive time.  This is a
pathwise continuity statement outside a null set depending on the time. -/
theorem IsStableLevyProcess.ae_leftLim_eq_eval
    (h : IsStableLevyProcess α μ X P) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (fun s => X s ω).leftLim t = X t ω := by
  letI : IsProbabilityMeasure μ := h.increments.strictlyStable.isProbabilityMeasure
  let times : ℕ → ℝ≥0 := fun n => t * ((n : ℝ≥0) / ((n : ℝ≥0) + 1))
  let gap : ℕ → ℝ≥0 := fun n => t - times n
  let scale : ℕ → ℝ := fun n => (gap n : ℝ) ^ (1 / α)
  let increment : ℕ → Ω → ℝ := fun n ω => X t ω - X (times n) ω
  let jump : Ω → ℝ := fun ω => X t ω - (fun s => X s ω).leftLim t

  have hratio : Tendsto (fun n : ℕ =>
      (n : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (𝓝 (1 : ℝ≥0)) := by
    simpa using (tendsto_natCast_div_add_atTop (𝕜 := ℝ≥0) (1 : ℝ≥0))
  have htimes : Tendsto times atTop (𝓝 t) := by
    simpa [times] using hratio.const_mul t
  have hratio_lt (n : ℕ) :
      (n : ℝ≥0) / ((n : ℝ≥0) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast Nat.lt_succ_self n
  have htimes_lt (n : ℕ) : times n < t := by
    dsimp [times]
    calc
      t * ((n : ℝ≥0) / ((n : ℝ≥0) + 1)) < t * 1 :=
        mul_lt_mul_of_pos_left (hratio_lt n) ht
      _ = t := by simp
  have htimes_left : Tendsto times atTop (𝓝[<] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨htimes, Filter.Eventually.of_forall fun n => htimes_lt n⟩
  have hgap : Tendsto gap atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    have h := hconst.sub htimes
    simpa [gap] using h
  have hgapReal : Tendsto (fun n => (gap n : ℝ)) atTop (𝓝 0) := by
    exact (continuous_subtype_val.tendsto (0 : ℝ≥0)).comp hgap
  have hexponent : 0 < (1 : ℝ) / α := one_div_pos.mpr h.increments.strictlyStable.1
  have hscale : Tendsto scale atTop (𝓝 0) := by
    have hp := (Real.continuousAt_rpow_const 0 (1 / α) (Or.inr hexponent.le)).tendsto
    have hpcomp := hp.comp hgapReal
    have hzero : (0 : ℝ) ^ (1 / α) = 0 := Real.zero_rpow hexponent.ne'
    rw [hzero] at hpcomp
    exact hpcomp

  have hscaled : TendstoInDistribution
      (fun n (x : ℝ) => scale n * x) atTop (fun _ : ℝ => 0)
      (fun _ : ℕ => μ) μ := by
    apply tendstoInDistribution_of_ae_tendsto
    · intro n
      fun_prop
    · fun_prop
    · filter_upwards with x
      have hx : Tendsto (fun n => scale n * x) atTop (𝓝 (0 * x)) :=
        hscale.mul_const x
      simpa using hx

  have hincrement_law (n : ℕ) :
      HasLaw (increment n) (μ.map fun x => scale n * x) P := by
    have hlaw := h.increments.increment_hasLaw (times n) t (le_of_lt (htimes_lt n))
    have hcoeff : scale n =
        ((t : ℝ) - (times n : ℝ)) ^ (1 / α) := by
      dsimp [scale, gap]
      rw [NNReal.coe_sub (le_of_lt (htimes_lt n))]
    rw [← hcoeff] at hlaw
    simpa [increment] using hlaw
  have hincrement_ident (n : ℕ) :
      IdentDistrib (increment n) (fun x : ℝ => scale n * x) P μ := by
    exact hincrement_law n |>.identDistrib
      ⟨(measurable_const.mul measurable_id).aemeasurable, rfl⟩
  have hincrement_to_zero : TendstoInDistribution increment atTop
      (fun _ : ℝ => 0) (fun _ : ℕ => P) μ := by
    refine ⟨fun n => (hincrement_ident n).aemeasurable_fst, ?_, ?_⟩
    · fun_prop
    · exact hscaled.tendsto.congr' <| Filter.Eventually.of_forall fun n => by
        apply Subtype.ext
        exact (hincrement_ident n).map_eq.symm

  have hae_tendsto : ∀ᵐ ω ∂P,
      Tendsto (fun n => increment n ω) atTop (𝓝 (jump ω)) := by
    filter_upwards [h.ae_cadlag] with ω hω
    have hleft := hω.tendsto_nhdsLT_leftLim t
    have hleftSeq := hleft.comp htimes_left
    have hsub : Tendsto (fun n => X t ω - X (times n) ω) atTop
        (𝓝 (X t ω - (fun s => X s ω).leftLim t)) :=
      tendsto_const_nhds.sub hleftSeq
    simpa [increment, jump] using hsub
  have hjump_meas : AEMeasurable jump P :=
    aemeasurable_of_tendsto_metrizable_ae atTop
      (fun n => (hincrement_law n).aemeasurable) hae_tendsto
  have hjump_dist : TendstoInDistribution increment atTop jump
      (fun _ : ℕ => P) P :=
    tendstoInDistribution_of_ae_tendsto
      (fun n => (hincrement_law n).aemeasurable) hjump_meas hae_tendsto
  have hunique := tendstoInDistribution_unique increment
    hincrement_to_zero hjump_dist
  have hjump_law : HasLaw jump (Measure.dirac 0) P := by
    refine ⟨hjump_meas, ?_⟩
    rw [← hunique]
    simp
  have hae_zero : ∀ᵐ ω ∂P, jump ω = 0 := by
    rw [hjump_law.ae_iff (p := fun x : ℝ => x = 0) (by fun_prop)]
    simp
  filter_upwards [hae_zero] with ω hω
  dsimp [jump] at hω
  linarith

/-- For a stable Lévy process, a closed oscillation bound observed at
rational times strictly before time one extends to the endpoint almost
surely. The only extra input is the path's half-open bound; endpoint
extension uses the fixed-time no-jump theorem above. -/
theorem IsStableLevyProcess.ae_rationalInteriorOscillationLe_implies_rationalCoordinateOscillationLe
    (h : IsStableLevyProcess α μ X P) (width : ℝ) :
    ∀ᵐ ω ∂P,
      (∀ s t : RationalCoordinate.UnitInterval, s < ⊤ → t < ⊤ →
        |X (RationalCoordinate.toNNReal s) ω - X (RationalCoordinate.toNNReal t) ω| ≤ width) →
      ∀ s t : RationalCoordinate.UnitInterval,
        |X (RationalCoordinate.toNNReal s) ω - X (RationalCoordinate.toNNReal t) ω| ≤ width := by
  have hcadlag := h.ae_cadlag
  have hnoJump := h.ae_leftLim_eq_eval 1 (by norm_num)
  filter_upwards [hcadlag, hnoJump] with ω hω hωjump
  intro hinterior s t
  have htoMono : Monotone RationalCoordinate.toUnitInterval := by
    intro q r hqr
    change ((q : ℚ) : ℝ) ≤ ((r : ℚ) : ℝ)
    exact_mod_cast hqr
  have hbotTop : (⊥ : unitInterval) < ⊤ := by
    norm_num [unitInterval]
  obtain ⟨u, _, hu, hulim⟩ :=
    RationalCoordinate.denseRange_toUnitInterval.exists_seq_strictMono_tendsto_of_lt
      htoMono hbotTop
  have htimeLimit : Tendsto (fun n => RationalCoordinate.toNNReal (u n)) atTop
      (𝓝 (1 : ℝ≥0)) := by
    rw [← NNReal.tendsto_coe]
    simpa [RationalCoordinate.toNNReal_coe, Function.comp_def] using
      (continuous_subtype_val.tendsto ⊤).comp hulim
  have htimeWithin : Tendsto (fun n => RationalCoordinate.toNNReal (u n)) atTop
      (𝓝[<] (1 : ℝ≥0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨htimeLimit, Filter.Eventually.of_forall fun n => ?_⟩
    have hbelow := (hu n).2
    have hbelowReal : ((u n : ℚ) : ℝ) < 1 := by
      change RationalCoordinate.toUnitInterval (u n) < ⊤ at hbelow
      exact hbelow
    have hbelowTime : (RationalCoordinate.toNNReal (u n) : ℝ) < 1 := by
      change ((u n : ℚ) : ℝ) < 1
      exact hbelowReal
    exact NNReal.coe_lt_coe.mp hbelowTime
  have hpathLimit : Tendsto (fun n => X (RationalCoordinate.toNNReal (u n)) ω) atTop
      (𝓝 (X 1 ω)) := by
    rw [← hωjump]
    exact (tendsto_leftLim_of_tendsto (hω.tendsto_nhdsLT 1)).comp htimeWithin
  have htopBound (q : RationalCoordinate.UnitInterval) (hq : q < ⊤) :
      |X (RationalCoordinate.toNNReal q) ω - X 1 ω| ≤ width := by
    have hdiff : Tendsto (fun n => X (RationalCoordinate.toNNReal q) ω -
        X (RationalCoordinate.toNNReal (u n)) ω) atTop
        (𝓝 (X (RationalCoordinate.toNNReal q) ω - X 1 ω)) :=
      tendsto_const_nhds.sub hpathLimit
    have habs : Tendsto (fun n => |X (RationalCoordinate.toNNReal q) ω -
        X (RationalCoordinate.toNNReal (u n)) ω|) atTop
        (𝓝 |X (RationalCoordinate.toNNReal q) ω - X 1 ω|) :=
      (continuous_abs.tendsto _).comp hdiff
    have hbounded : ∀ᶠ n in atTop,
        |X (RationalCoordinate.toNNReal q) ω - X (RationalCoordinate.toNNReal (u n)) ω| ∈
          Set.Iic width :=
      Filter.Eventually.of_forall fun n => hinterior q (u n) hq (by
        change (u n : ℚ) < 1
        have hbelow := (hu n).2
        have hbelowReal : ((u n : ℚ) : ℝ) < 1 := by
          change RationalCoordinate.toUnitInterval (u n) < ⊤ at hbelow
          exact hbelow
        exact_mod_cast hbelowReal)
    exact isClosed_Iic.mem_of_tendsto habs hbounded
  by_cases hs : s = ⊤
  · subst s
    by_cases ht : t = ⊤
    · have hwidth0 : 0 ≤ width := by
        have hbotTopQ : (⊥ : RationalCoordinate.UnitInterval) < ⊤ := by
          change (0 : ℚ) < 1
          norm_num
        simpa using hinterior ⊥ ⊥ hbotTopQ hbotTopQ
      simp [ht, hwidth0]
    · have ht' : t < ⊤ := lt_of_le_of_ne le_top ht
      have htopTime : RationalCoordinate.toNNReal ⊤ = 1 := RationalCoordinate.toNNReal_top
      rw [htopTime]
      simpa [abs_sub_comm] using htopBound t ht'
  · by_cases ht : t = ⊤
    · subst t
      rw [RationalCoordinate.toNNReal_top]
      exact htopBound s (lt_of_le_of_ne le_top hs)
    · exact hinterior s t (lt_of_le_of_ne le_top hs) (lt_of_le_of_ne le_top ht)

end ProbabilityTheory

end
