/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Marked.Basic
public import Probability.Distributions.Moments.Real
public import MeasureTheory.Measure.Tails.Quadratic
public import Analysis.Asymptotics.Scale.Basic
import Probability.Kernel.Survival.Return.NoiseRestriction
import Mathlib.Topology.Order.LeftRight
import all Probability.Process.RandomWalk.SmallDeviation.Marked.Lemmas.ReturnBlocks

/-!
# Finite-variance lower bounds for long marked affine corridors

## Public declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Marked.eventually_affineCorridorProbability_ge_exp_of_finiteVariance`:
  let `(Xⱼ,Bⱼ)` be IID with an arbitrary joint law, `EX=0`,
  `EX²=σ²>0`, and `t² P(B>t)→0`. If `Lₙ→∞`, `Hₙ>0` eventually
  and `Lₙ²/Hₙ→0`,
  then for `c≥0`, `α>0` and `d>π²σ²/2`, eventually
  `exp(-dHₙ/Lₙ²) ≤ P(-Lₙ/2 ≤ S_k-ck/Lₙ² ≤ Lₙ/2 (1≤k≤Hₙ),
  Bⱼ≤αLₙ (j<Hₙ))`.

The displacement and its mark may be correlated. The proof applies the
weak-tail union bound only on diffusive return blocks, then iterates the
existing partial-step return kernel. Increasing the fixed diffusion-block
constant absorbs the per-block factor `1/2` without changing the sharp
small-deviation constant. No centered conditioned increment law is assumed.

This is the zero-tail-constant lower-bound block argument of B. Mallein,
*Necessary and sufficient conditions for the convergence of the consistent
maximal displacement of the branching random walk*, §2.2, Theorem 2.3 and
proof of Lemma 2.5, arXiv:1510.00602v2, here including deterministic drift
`c/Lₙ²`. Unmarked endpoint windows use the existing finite-variance
Mogul'skii theorem, Theorem 3 of *Small Deviations in a Space of Trajectories*,
A. A. Mogul'skii, DOI 10.1137/1119081.
-/

@[expose] public section
namespace ProbabilityTheory.RandomWalk.SmallDeviation.Marked
open _root_.MeasureTheory Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

/-- The sharp finite-variance corridor lower bound persists under a correlated
weak-quadratic-tail mark constraint on the entire long time interval.
This specializes the zero-tail-constant block argument in B. Mallein,
*Necessary and sufficient conditions for the convergence of the consistent
maximal displacement of the branching random walk*, §2.2, Theorem 2.3
(arXiv:1510.00602v2), to a centered affine corridor. -/
theorem eventually_affineCorridorProbability_ge_exp_of_finiteVariance
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {sigma c α d : ℝ}
    (hν : IsCenteredSecondMoment (ν.map Prod.fst) (sigma ^ 2))
    (hσ : 0 < sigma) (htail : HasVanishingQuadraticTail ν Prod.snd)
    (hc : 0 ≤ c) (hα : 0 < α)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    {scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    (hscale : Tendsto scale atTop atTop)
    (horizonPos : ∀ᶠ n in atTop, 0 < horizon n)
    (hsmall : Tendsto (fun n => scale n ^ 2 / (horizon n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-d * (horizon n : ℝ) / scale n ^ 2)) ≤
      iidSequenceLaw ν
        (corridorEvent (-(scale n / 2)) (scale n / 2)
          (c / scale n ^ 2) (α * scale n) (horizon n) 0) := by
  let κ := (Real.pi ^ 2 / 2) * sigma ^ 2
  have hneigh : ∀ᶠ w : ℝ in 𝓝 1, (1 / 2 : ℝ) < w ∧ κ < d * w ^ 2 := by
    have hcont : ContinuousAt (fun w : ℝ => d * w ^ 2) 1 := by fun_prop
    have hr := hcont.tendsto.eventually (Ioi_mem_nhds (show κ < d * 1 ^ 2 by simpa [κ] using hd))
    filter_upwards [hr, (show ∀ᶠ w : ℝ in 𝓝 1, (1 / 2 : ℝ) < w from
      Ioi_mem_nhds (by norm_num))] with w h1 h2
    exact ⟨h2, h1⟩
  obtain ⟨w, hw1, hw, hkw⟩ := hneigh.exists_lt
  have hw0 : 0 < w := by linarith
  obtain ⟨d₀, hκd₀, hd₀⟩ := exists_between hkw
  have hgap : 0 < d - d₀ / w ^ 2 := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hw0)).2 hd₀
    linarith
  obtain ⟨T₀, hT₀, hblocks⟩ := exists_eventually_returnBlock_ge ν hν hσ hw hw1 hκd₀
  let T := max T₀ (max 1 (Real.log 4 / (d - d₀ / w ^ 2))) + 1
  have hT : T₀ < T := by dsimp [T]; linarith [le_max_left T₀ (max 1 (Real.log 4 / (d - d₀ / w ^ 2)))]
  have hTpos : 0 < T := lt_of_le_of_lt hT₀ hT
  have hlarge : Real.log 4 / (d - d₀ / w ^ 2) < T := by
    dsimp [T]
    linarith [le_max_right T₀ (max 1 (Real.log 4 / (d - d₀ / w ^ 2))),
      le_max_right (1 : ℝ) (Real.log 4 / (d - d₀ / w ^ 2))]
  let p := Real.exp (-d₀ * T / w ^ 2) / 2
  have hp : 0 < p := by dsimp [p]; positivity
  have hpless : p < Real.exp (-d₀ * T / w ^ 2) := by dsimp [p]; nlinarith [Real.exp_pos (-d₀ * T / w ^ 2)]
  let e := (1 - w) / 100
  have he : 0 < e := by dsimp [e]; positivity
  let step n := killedMarkedStep (-(scale n / 2)) (scale n / 2) (c / scale n ^ 2)
  let core n := Set.Icc (-3 * e * scale n) (3 * e * scale n)
  let length := Asymptotics.diffusiveBlockLength T scale
  have hrowENN := hblocks T hT hscale c hc p hpless
  have hrow : ∀ᶠ n in atTop, ∀ x : core n,
      p ≤ (Kernel.returnKernel
        (Kernel.ofPartialStep ν (step n) (killedMarkedStep_measurable _ _ _))
        (core n) measurableSet_Icc (length n) x Set.univ).toReal := by
    filter_upwards [hrowENN] with n hn
    intro x
    have hm := ENNReal.toReal_mono (measure_ne_top _ _) (hn x)
    simpa only [ENNReal.toReal_ofReal hp.le] using hm
  have hlen : ∀ᶠ n in atTop, (length n : ℝ) ≤ T * scale n ^ 2 := by
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    exact Nat.floor_le (by positivity)
  have hpos : ∀ᶠ n in atTop, 0 < length n :=
    (Asymptotics.tendsto_diffusiveBlockLength_atTop_of_tendsto_atTop
      hscale hTpos).eventually_gt_atTop 0
  have hret := Kernel.eventually_pow_le_survival_restrictNoise ν step
    (fun _ => killedMarkedStep_measurable _ _ _) core (fun _ => measurableSet_Icc)
    measurable_snd htail hscale hα hp hlen hpos hrow
  let q := -d₀ * T / w ^ 2 - Real.log 4
  have hqexp : Real.exp q = p / 2 := by
    dsimp [q, p]
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    ring
  have hqbudget : -d < q / T := by
    have hb := (div_lt_iff₀ hgap).1 hlarge
    dsimp [q]
    apply (lt_div_iff₀ hTpos).2
    have heq : -d₀ * T / w ^ 2 = -(d₀ / w ^ 2) * T := by ring
    rw [heq]
    nlinarith only [hb]
  have hlenRatio := Asymptotics.tendsto_floorBlockLength_div_sq_of_tendsto_atTop hscale hTpos
  have hcount := Asymptotics.tendsto_succ_quotientBlockCount_mul_scale_div
    (horizon := horizon) (scale := fun n => scale n ^ 2)
    (Eventually.of_forall (fun n => sq_nonneg (scale n))) hpos horizonPos hlenRatio hTpos hsmall
  have hnormalized : Tendsto (fun n =>
      q * ((horizon n / length n + 1 : ℕ) : ℝ) * scale n ^ 2 / (horizon n : ℝ))
      atTop (𝓝 (q / T)) := by
    simpa only [mul_one_div, mul_div_assoc, mul_assoc, length] using hcount.const_mul q
  have hcost := hnormalized.eventually (Ioi_mem_nhds hqbudget)
  filter_upwards [hret, hcost, hscale.eventually_gt_atTop 0, horizonPos]
    with n hn hcostN hscaleN hnat
  let x : core n := ⟨0, by dsimp [core]; constructor <;> nlinarith [mul_pos he hscaleN]⟩
  have hpath := hn (horizon n) x
  have hevent : {ω | Kernel.SurvivesPrefix (step n) (horizon n) (x : ℝ) ω ∧
      ∀ j < horizon n, (ω j).2 ≤ α * scale n} =
      corridorEvent (-(scale n / 2)) (scale n / 2)
        (c / scale n ^ 2) (α * scale n) (horizon n) 0 := by
    ext ω
    exact and_congr (survivesPrefix_killedMarkedStep_iff _ _ _ _ _ ω) Iff.rfl
  rw [hevent] at hpath
  have hfac : -d * (horizon n : ℝ) / scale n ^ 2 ≤
      q * ((horizon n / length n + 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hscaleN)).2
    have hh := (lt_div_iff₀ (show (0 : ℝ) < horizon n by exact_mod_cast hnat)).1 hcostN
    linarith
  refine (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hfac)).trans ?_
  calc
    ENNReal.ofReal (Real.exp (q * ((horizon n / length n + 1 : ℕ) : ℝ))) =
        ENNReal.ofReal (Real.exp q) ^ (horizon n / length n + 1) := by
      rw [mul_comm, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_nonneg q)]
    _ = ENNReal.ofReal (p / 2) ^ (horizon n / length n + 1) := by rw [hqexp]
    _ ≤ _ := hpath

end ProbabilityTheory.RandomWalk.SmallDeviation.Marked
