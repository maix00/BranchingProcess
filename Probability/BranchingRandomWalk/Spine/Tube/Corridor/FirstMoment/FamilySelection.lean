/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.FamilySelection
public import Probability.BranchingRandomWalk.Assumptions.SpinalWeightTail
public import Probability.Process.RandomWalk.Path.Corridor.Affine
public import Probability.Distributions.Moments.Real
import Probability.Process.RandomWalk.SmallDeviation.Marked.FiniteVarianceLower
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceUpper.Basic
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.PathCount

/-!
# Actual family-cutoff corridor first moments under weak spinal tails

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.eventually_lintegral_pathGeneration_affineCorridor_cutoff_ge_of_finiteVariance`:
  with the original boundary-normalized centered spine of variance `σ²>0`
  and Mallein's weak spinal weight tail, let `μₙ` select precisely families
  with `W≤exp(αLₙ)`. For internal `a,b∈(-1/2,1/2)`, `ρ,α>0`, `c≥0`,
  `d>π²σ²/2`, `Lₙ→∞` and `Lₙ²/Hₙ→0`, eventually
  `exp((b-ρ-a)Lₙ+(c-d)Hₙ/Lₙ²)≤E_μₙ Z_Hₙ`, where the actual existing
  path count starts at zero, has lower edge `-(a+1/2)Lₙ`, width `Lₙ`,
  slope `c/Lₙ²`, and terminal upper bound
  `(b+ρ-a)Lₙ+cHₙ/Lₙ²`.

* `ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_sum_pathGeneration_affineCorridorPrefix_selectFamily_le_exp_of_finiteVariance`:
  under original boundary normalization and centered spinal variance `σ²>0`,
  for `c≥0`, `0<d<π²σ²/2`, `lower∈[-L,0]` and every measurable family
  selection `A`, uniformly in `H` and large `L`,
  `E_μA ∑_(j≤H) Zⱼ(prefix) ≤ (H+1) exp(lower+L+√L+max(c-d,0)H/L²)`.
  This upper estimate uses no reproductive weak-tail hypothesis.

Only the original spinal law is centered and boundary-normalized. The mark
is `log₊W`, with its dependence on the chosen displacement retained. Every
strict ancestor of a counted path must pass the actual total-weight cutoff.
The terminal endpoint's own family is not inspected. No finite untruncated
cross moment or logarithmic second moment is assumed.

This is the family-cutoff first-moment step in B. Mallein, *N-branching
random walk with α-stable spine*, proof of Lemma 3.4, arXiv:1503.03762v2,
and *Necessary and sufficient conditions for the convergence of the
consistent maximal displacement of the branching random walk*, proof of
Lemma 3.4, arXiv:1510.00602v2. The marked affine estimate is its §2.2,
Theorem 2.3 and proof of Lemma 2.5, specialized to zero quadratic tail constant.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Filter Combinatorics.Branching
open BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk ProbabilityTheory.RandomWalk.SmallDeviation.Marked
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

private lemma map_selectFamily_weight_eq_positiveLog
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X))
    (hfinite : ∀ᵐ ξ ∂μ, totalPotentialWeight φ (-1) ξ ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.map (Step.selectFamily {ξ | totalPotentialWeight φ (-1) ξ ≤ ENNReal.ofReal (Real.exp t)}) =
      μ.map (Step.selectFamily {ξ | max (logTotalPotentialWeight φ ξ) 0 ≤ t}) := by
  apply Measure.map_congr
  filter_upwards [hfinite] with ξ hξ
  have heq : totalPotentialWeight φ (-1) ξ ≤ ENNReal.ofReal (Real.exp t) ↔
      max (logTotalPotentialWeight φ ξ) 0 ≤ t := by
    by_cases hz : totalPotentialWeight φ (-1) ξ = 0
    · simp [logTotalPotentialWeight, hz, ht]
    · rw [← ENNReal.toReal_le_toReal hξ ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (Real.exp_nonneg t), ← Real.log_le_iff_le_exp (ENNReal.toReal_pos hz hξ)]
      simp only [max_le_iff, ht, and_true, logTotalPotentialWeight]
  simp only [Step.selectFamily, Set.mem_ofPred_eq, heq]

set_option maxHeartbeats 600000 in
/-- The actual family-truncated generation count has the marked-spine first
moment lower bound in the proof of B. Mallein, *N-branching random walk
with α-stable spine*, Lemma 3.4 (arXiv:1503.03762v2), under the finite-variance
weak-tail hypothesis. -/
theorem eventually_lintegral_pathGeneration_affineCorridor_cutoff_ge_of_finiteVariance
    {ι X : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {sigma c α d a b ρ : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) (sigma ^ 2))
    (hσ : 0 < sigma) (htail : HasSpinalWeightTail φ μ)
    (hc : 0 ≤ c) (hα : 0 < α) (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ)
    {scale : ℕ → ℝ} {horizon : ℕ → ℕ} (hscale : Tendsto scale atTop atTop)
    (horizonPos : ∀ᶠ n in atTop, 0 < horizon n)
    (hsmall : Tendsto (fun n => scale n ^ 2 / (horizon n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (Real.exp ((b - ρ - a) * scale n +
        (c - d) * (horizon n : ℝ) / scale n ^ 2)) ≤
      ∫⁻ field, pathGeneration φ (horizon n)
        ((affineCorridorThrough (horizon n) (-(a + 1 / 2) * scale n)
          (c / scale n ^ 2) (scale n)
          ((b + ρ - a) * scale n + c * (horizon n : ℝ) / scale n ^ 2)).indicator
          (fun _ => (1 : ℝ≥0∞))) 0 field
        ∂offspringFieldLaw (μ.map (Step.selectFamily
          {ξ | totalPotentialWeight φ (-1) ξ ≤ ENNReal.ofReal (Real.exp (α * scale n))})) := by
  let mark := fun ξ : Step ι X => max (logTotalPotentialWeight φ ξ) 0
  have hm : Measurable mark := (logTotalPotentialWeight_measurable φ).max measurable_const
  let ν := tiltedMarkedPotentialLaw φ (-1) μ (fun p => mark p.1)
  let : IsProbabilityMeasure ν := tiltedMarkedPotentialLaw_isProbability φ μ hboundary (hm.comp measurable_fst)
  have hν : IsCenteredSecondMoment (ν.map Prod.fst) (sigma ^ 2) := by
    have hf : ν.map Prod.fst = tiltedPotentialLaw φ (-1) μ := by
      simpa only [ν, Function.comp_def] using
        tiltedMarkedPotentialLaw_fst φ (-1) μ (hm.comp measurable_fst)
    rw [hf]
    exact hcentered
  have hsq : Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw φ (-1) μ) := by
    by_contra hn
    have hh := integral_undef hn
    rw [hcentered.2] at hh
    exact (sq_pos_of_pos hσ).ne' hh
  have hraw := (hasSpinalWeightTail_iff_totalWeightTail φ μ hboundary hsq).mp htail
  have hplus := (hasVanishingQuadraticTail_max_const_iff (μ := μ.withDensity
    (totalPotentialWeight φ (-1))) (f := logTotalPotentialWeight φ) 0).2 hraw
  have hfamily : HasVanishingQuadraticTail (tiltedFamilyChildLaw φ (-1) μ)
      (fun p => mark p.1) := by
    apply (hasVanishingQuadraticTail_map_iff Prod.fst measurable_fst mark hm).1
    rw [tiltedFamilyChildLaw_fst]
    exact hplus
  have hread : Measurable (fun p : Step ι X × ι => (p.1.potentialValue' φ p.2, mark p.1)) :=
    (measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)).prodMk
      (hm.comp measurable_fst)
  have hmarks : HasVanishingQuadraticTail ν Prod.snd :=
    (hasVanishingQuadraticTail_map_iff _ hread Prod.snd measurable_snd).2 hfamily
  have hbound := eventually_lintegral_exp_affineCorridorEndpoint_ge_of_finiteVariance
    (θ := 1) ν hν hσ hmarks hc hα hd ha ha' hb hb' hρ (by norm_num) hscale horizonPos hsmall
  filter_upwards [hbound, hscale.eventually_gt_atTop 0] with n hn hL
  let L := scale n
  let H := horizon n
  let δ := c / L ^ 2
  let U := (b + ρ - a) * L + c * (H : ℝ) / L ^ 2
  let E := corridorEndpointEvent (-(L / 2)) (L / 2) δ (α * L) H (a * L)
    (Set.Icc ((b - ρ) * L) ((b + ρ) * L))
  let C := affineCorridorThrough H (-(a + 1 / 2) * L) δ L U
  have hC : MeasurableSet C := measurableSet_affineCorridorThrough _ _ _ _ _
  have hsum (ω : ℕ → ℝ × ℝ) (k : ℕ) :
      AdditivePath.displacement k (fun j => (ω j).1 - δ) =
        AdditivePath.displacement k (fun j => (ω j).1) - (k : ℝ) * δ := by
    simp [AdditivePath.displacement, Finset.sum_sub_distrib]
  have hfit (ω : ℕ → ℝ × ℝ) (hω : ω ∈ E) : history H 0 (fun j => (ω j).1) ∈ C := by
    constructor
    · intro k
      simp only [history_apply, zero_add]
      by_cases hk : k.val = 0
      · simp only [hk, Nat.cast_zero, mul_zero, AdditivePath.displacement_zero, add_zero]
        constructor <;> nlinarith only [ha.le, ha'.le, hL]
      · let j : Fin H := ⟨k.val - 1, by omega⟩
        have hp := hω.1.1 j
        have hj : j.val + 1 = k.val := by dsimp [j]; omega
        rw [hj, hsum] at hp
        constructor <;> nlinarith only [hp.1, hp.2]
    · have ht := hω.2.2
      rw [hsum] at ht
      simp only [history_apply, zero_add]
      dsimp [U]
      rw [show c * (H : ℝ) / L ^ 2 = (H : ℝ) * δ by dsimp [δ]; ring]
      nlinarith only [ht]
  have hcut := map_selectFamily_weight_eq_positiveLog φ μ
    (hboundary.ae_totalPotentialWeight_ne_top φ μ) (mul_pos hα hL).le
  rw [hcut]
  have hmany := pathManyToOne_selectFamily φ μ hboundary hm
    (accepted := Set.Iic (α * L)) measurableSet_Iic H
    (F := C.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hC) 0
  change (∫⁻ field, pathGeneration φ H (C.indicator (fun _ => (1 : ℝ≥0∞))) 0 field
    ∂offspringFieldLaw (μ.map (Step.selectFamily
      {ξ | max (logTotalPotentialWeight φ ξ) 0 ≤ α * scale n}))) = _ at hmany
  rw [hmany]
  have hn' : ENNReal.ofReal (Real.exp ((b - ρ - a) * L + (c - d) * (H : ℝ) / L ^ 2)) ≤
      ∫⁻ ω in E, ENNReal.ofReal (Real.exp (AdditivePath.displacement H (fun j => (ω j).1)))
        ∂iidSequenceLaw ν := by
    rw [show (b - ρ - a) * L + (c - d) * (H : ℝ) / L ^ 2 =
      (b - ρ - a) * L + c * (H : ℝ) / L ^ 2 - d * (H : ℝ) / L ^ 2 by ring]
    simpa only [one_mul] using hn
  refine hn'.trans ?_
  rw [← lintegral_indicator (measurableSet_corridorEndpointEvent _ _ _ _ _ _ measurableSet_Icc)]
  apply lintegral_mono
  intro ω
  by_cases hω : ω ∈ E
  · rw [Set.indicator_of_mem hω]
    have hkeep : ∀ j < H, (ω j).2 ∈ Set.Iic (α * L) := hω.1.2
    simp only [ite_eq_left hkeep, Set.indicator_of_mem (hfit ω hω), mul_one, le_refl]
  · rw [Set.indicator_of_notMem hω]
    exact bot_le

/-- A uniform affine-tube first-moment bound controls cumulative population
after arbitrary measurable whole-family selection. This is the population
estimate used with Markov's inequality in B. Mallein, *N-branching random
walk with α-stable spine*, proof of Lemma 3.4 (arXiv:1503.03762v2). -/
theorem exists_lintegral_sum_pathGeneration_affineCorridorPrefix_selectFamily_le_exp_of_finiteVariance
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {variance c d : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) variance)
    (hvariance : 0 < variance) (hc : 0 ≤ c) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ A : Set (Step ι X), MeasurableSet A →
      ∀ lower : ℝ, -L ≤ lower → lower ≤ 0 → ∀ H : ℕ,
      (∫⁻ field, ∑ j : Fin (H + 1), pathGeneration φ j.val
        ((affineCorridorPrefix j.val lower (c / L ^ 2) L).indicator
          (fun _ => (1 : ℝ≥0∞))) 0 field
        ∂offspringFieldLaw (μ.map (Step.selectFamily A))) ≤
      ((H : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp
        (lower + L + L ^ (1 / 2 : ℝ) + max (c - d) 0 * (H : ℝ) / L ^ 2)) := by
  let ν := tiltedPotentialLaw φ (-1) μ
  let : IsProbabilityMeasure ν := tiltedPotentialLaw_isProbability φ μ hboundary
  obtain ⟨L₀, hL₀, htube⟩ := SmallDeviation.DriftedTube.exists_driftedTubeProbability_le_exp_of_finiteVariance
    ν hcentered hvariance (by norm_num : (0 : ℝ) < 1 / 2) hc hd hcritical
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL A hA lower hlower hupper H
  let B := lower + L + L ^ (1 / 2 : ℝ) + max (c - d) 0 * (H : ℝ) / L ^ 2
  have hpoint (j : Fin (H + 1)) :
      (∫⁻ field, pathGeneration φ j.val
        ((affineCorridorPrefix j.val lower (c / L ^ 2) L).indicator
          (fun _ => (1 : ℝ≥0∞))) 0 field ∂offspringFieldLaw (μ.map (Step.selectFamily A))) ≤
        ENNReal.ofReal (Real.exp B) := by
    let C := affineCorridorPrefix j.val lower (c / L ^ 2) L
    have hC : MeasurableSet C := measurableSet_affineCorridorPrefix _ _ _ _
    have hdom := lintegral_pathGeneration_selectFamily_le φ μ hA j.val
      (F := C.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hC) 0
    have hmean := lintegral_pathGeneration_le_exp_mul_spineProbability φ μ hboundary j.val 0
      (lower + c / L ^ 2 * (j.val : ℝ) + L) C hC (fun h hh => (hh (Fin.last j.val)).2)
    have hprob : tiltedIncrementFieldLaw φ μ {z | history j.val 0 z ∈ C} ≤
        ENNReal.ofReal (Real.exp (L ^ (1 / 2 : ℝ) - d * ((j.val : ℝ) / L ^ 2))) := by
      refine (measure_mono
        (SmallDeviation.DriftedTube.affineCorridorPrefix_history_subset_driftedTubeEvent
          j.val 0 lower c L)).trans ?_
      change iidSequenceLaw ν (SmallDeviation.DriftedTube.driftedTubeEvent j.val L c (lower - 0)) ≤ _
      rw [sub_zero, ← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (htube L hL lower hlower hupper j.val)
    refine hdom.trans (hmean.trans ((mul_le_mul' le_rfl hprob).trans ?_))
    rw [sub_zero, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right (le_max_left (c - d) 0) (Nat.cast_nonneg j.val)
    have hj : (j.val : ℝ) ≤ H := by exact_mod_cast (show j.val ≤ H by omega)
    have h2 := mul_le_mul_of_nonneg_left hj (le_max_right (c - d) 0)
    have h3 := div_le_div_of_nonneg_right (h1.trans h2) (sq_nonneg L)
    dsimp [B]
    rw [sub_mul, sub_div] at h3
    rw [div_mul_eq_mul_div, ← mul_div_assoc]
    linarith only [h3]
  rw [lintegral_finsetSum' Finset.univ (fun j _ =>
    (pathGeneration_measurable φ j.val
      (measurable_const.indicator (measurableSet_affineCorridorPrefix _ _ _ _)) 0).aemeasurable)]
  calc
    _ ≤ ∑ _j : Fin (H + 1), ENNReal.ofReal (Real.exp B) := Finset.sum_le_sum (fun j _ => hpoint j)
    _ = _ := by simp [B]

end ProbabilityTheory.BranchingRandomWalk.Spine
