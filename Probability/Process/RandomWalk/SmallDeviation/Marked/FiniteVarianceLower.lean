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
import Probability.Kernel.Step.Noise.QuadraticTail
import Probability.Kernel.Survival.Return.Basic
import Mathlib.Topology.Order.LeftRight
import all Probability.Process.RandomWalk.SmallDeviation.Marked.Lemmas.TransitionBlocks

/-!
# Finite-variance lower bounds for long marked affine corridors

## Public declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Marked.eventually_affineCorridorEndpointProbability_ge_exp_of_finiteVariance`:
  under the same joint IID, moment, weak-tail and scale hypotheses below,
  for `a,b∈(-1/2,1/2)` and `ρ>0`, the marked corridor from `aLₙ`
  ending in `[(b-ρ)Lₙ,(b+ρ)Lₙ]` has probability at least
  `exp(-dHₙ/Lₙ²)` eventually.
* `ProbabilityTheory.RandomWalk.SmallDeviation.Marked.eventually_lintegral_exp_affineCorridorEndpoint_ge_of_finiteVariance`:
  for `θ≥0`, the same event `Eₙ` satisfies
  `exp(θ((b-ρ-a)Lₙ+cHₙ/Lₙ²)-dHₙ/Lₙ²) ≤ E[exp(θS_Hₙ); Eₙ]`.
* `ProbabilityTheory.RandomWalk.SmallDeviation.Marked.eventually_affineCorridorProbability_ge_exp_of_finiteVariance`:
  let `(Xⱼ,Bⱼ)` be IID with an arbitrary joint law, `EX=0`,
  `EX²=σ²>0`, and `t² P(B>t)→0`. If `Lₙ→∞`, `Hₙ>0` eventually
  and `Lₙ²/Hₙ→0`,
  then for `c≥0`, `α>0` and `d>π²σ²/2`, eventually
  `exp(-dHₙ/Lₙ²) ≤ P(-Lₙ/2 ≤ S_k-ck/Lₙ² ≤ Lₙ/2 (1≤k≤Hₙ),
  Bⱼ≤αLₙ (j<Hₙ))`.

The displacement and its mark may be correlated. The proof applies the
weak-tail union bound only on diffusive return blocks, then iterates the
existing partial-step return kernel. Entrance and terminal blocks use the
same transition estimate; the last block has length between one and two
return-block lengths and absorbs the remainder exactly. Increasing the fixed diffusion-block
constant absorbs the fixed per-block probability loss without changing the sharp
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

set_option maxHeartbeats 800000 in
/-- The zero-tail-constant lower-bound argument of B. Mallein,
*Necessary and sufficient conditions for the convergence of the consistent
maximal displacement of the branching random walk*, Theorem 2.3 and proof
of Lemma 2.5 (arXiv:1510.00602v2), for affine corridors with arbitrary
internal initial fraction and prescribed internal terminal window. -/
theorem eventually_affineCorridorEndpointProbability_ge_exp_of_finiteVariance
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {sigma c α d a b ρ : ℝ}
    (hν : IsCenteredSecondMoment (ν.map Prod.fst) (sigma ^ 2))
    (hσ : 0 < sigma) (htail : HasVanishingQuadraticTail ν Prod.snd)
    (hc : 0 ≤ c) (hα : 0 < α)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ)
    {scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    (hscale : Tendsto scale atTop atTop)
    (horizonPos : ∀ᶠ n in atTop, 0 < horizon n)
    (hsmall : Tendsto (fun n => scale n ^ 2 / (horizon n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-d * (horizon n : ℝ) / scale n ^ 2)) ≤
      iidSequenceLaw ν
        (corridorEndpointEvent (-(scale n / 2)) (scale n / 2)
          (c / scale n ^ 2) (α * scale n) (horizon n) (a * scale n)
          (Set.Icc ((b - ρ) * scale n) ((b + ρ) * scale n))) := by
  let κ := (Real.pi ^ 2 / 2) * sigma ^ 2
  have pos (f : ℝ → ℝ) (hf : ContinuousAt f 1) (h : 0 < f 1) :
      ∀ᶠ w in 𝓝 1, 0 < f w := hf.tendsto.eventually (Ioi_mem_nhds h)
  have hneigh : ∀ᶠ w : ℝ in 𝓝 1,
      (1 / 2 : ℝ) < w ∧ κ < d * w ^ 2 ∧
      -w / 2 < a ∧ a < w / 2 ∧
      -w / 2 + 4 * ((1 - w) / 100) < b ∧ b < w / 2 - 4 * ((1 - w) / 100) ∧
      3 * ((1 - w) / 100) < ρ := by
    filter_upwards [pos (fun w => w - 1 / 2) (by fun_prop) (by norm_num),
      pos (fun w => d * w ^ 2 - κ) (by fun_prop) (by dsimp [κ]; nlinarith),
      pos (fun w => a + w / 2) (by fun_prop) (by linarith),
      pos (fun w => w / 2 - a) (by fun_prop) (by linarith),
      pos (fun w => b + w / 2 - 4 * ((1 - w) / 100)) (by fun_prop) (by linarith),
      pos (fun w => w / 2 - 4 * ((1 - w) / 100) - b) (by fun_prop) (by linarith),
      pos (fun w => ρ - 3 * ((1 - w) / 100)) (by fun_prop) (by linarith)]
      with w h1 h2 h3 h4 h5 h6 h7
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith⟩
  obtain ⟨w, hw1, hw, hkw, haw, haw', hbw, hbw', hρw⟩ := hneigh.exists_lt
  have hw0 : 0 < w := by linarith
  let e := (1 - w) / 100
  have he : 0 < e := by dsimp [e]; positivity
  have hfit : w / 2 + 4 * e ≤ 1 / 2 := by dsimp [e]; linarith
  have hcore : 0 < w / 2 - 4 * e := by change _ at hbw hbw'; linarith
  obtain ⟨d₀, hκd₀, hd₀⟩ := exists_between hkw
  have hgap : 0 < d - d₀ / w ^ 2 := by
    have h := (div_lt_iff₀ (sq_pos_of_pos hw0)).2 hd₀
    linarith
  have hlocal (a b : ℝ) := exists_eventually_transitionBlock_ge (a := a) (b := b) (d := d₀) ν hν hσ hw0 he
  obtain ⟨Tᵢ, hTᵢ, hentry⟩ := hlocal a 0 haw haw' (by linarith) (by linarith) hfit hκd₀
  obtain ⟨Tᵣ, hTᵣ, hreturn⟩ := hlocal 0 0 (by linarith : -w / 2 < (0 : ℝ))
    (by linarith : (0 : ℝ) < w / 2) (by linarith) (by linarith) hfit hκd₀
  obtain ⟨Tₑ, hTₑ, hend⟩ := hlocal 0 b (by linarith : -w / 2 < (0 : ℝ))
    (by linarith : (0 : ℝ) < w / 2) hbw hbw' hfit hκd₀
  let budget := max 1 (Real.log 4 / (d - d₀ / w ^ 2))
  have hbudget : 0 ≤ budget := le_trans (by norm_num) (le_max_left 1 _)
  let T := Tᵢ + Tᵣ + Tₑ + budget + 1
  have hTi : Tᵢ < T := by dsimp [T]; linarith only [hTᵣ, hTₑ, hbudget]
  have hTr : Tᵣ < T := by dsimp [T]; linarith only [hTᵢ, hTₑ, hbudget]
  have hTe : Tₑ < T := by dsimp [T]; linarith only [hTᵢ, hTᵣ, hbudget]
  have hTpos : 0 < T := lt_of_le_of_lt hTᵢ hTi
  have hlarge : Real.log 4 / (d - d₀ / w ^ 2) < T := by
    have h := le_max_right (1 : ℝ) (Real.log 4 / (d - d₀ / w ^ 2))
    change _ ≤ budget at h
    dsimp [T]
    linarith only [hTᵢ, hTᵣ, hTₑ, h]
  let p := Real.exp (-d₀ * T / w ^ 2) / 2
  let pEnd := Real.exp (-d₀ * 2 * T / w ^ 2) / 2
  have hp : 0 < p := by dsimp [p]; positivity
  have hpEnd : 0 < pEnd := by dsimp [pEnd]; positivity
  have hpless : p < Real.exp (-d₀ * T / w ^ 2) := by
    dsimp [p]; nlinarith [Real.exp_pos (-d₀ * T / w ^ 2)]
  have hpEndless : pEnd < Real.exp (-d₀ * 2 * T / w ^ 2) := by
    dsimp [pEnd]; nlinarith [Real.exp_pos (-d₀ * 2 * T / w ^ 2)]
  have hi := hentry T hTi 1 (by omega) hscale c hc p (by simpa using hpless)
  have hr := hreturn T hTr 1 (by omega) hscale c hc p (by simpa using hpless)
  have hf := hend T hTe 2 (by omega) hscale c hc pEnd (by simpa using hpEndless)
  let block := Asymptotics.diffusiveBlockLength T scale
  let step n := killedMarkedStep (-(scale n / 2)) (scale n / 2) (c / scale n ^ 2)
  let core n := Set.Icc ((0 - 3 * e) * scale n) ((0 + 3 * e) * scale n)
  let lastCore n := Set.Icc ((b - 3 * e) * scale n) ((b + 3 * e) * scale n)
  let constrained n := Kernel.restrictNoise (step n) {z | z.2 ≤ α * scale n}
  have hcon n : Measurable (Function.uncurry (constrained n)) :=
    Kernel.measurable_restrictNoise _ (killedMarkedStep_measurable _ _ _)
      (measurableSet_le measurable_snd measurable_const)
  let K n := Kernel.ofPartialStep ν (constrained n) (hcon n)
  have hlen : ∀ᶠ n in atTop, (2 * block n : ℕ) ≤ (2 * T) * scale n ^ 2 := by
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    have hfl : (block n : ℝ) ≤ T * scale n ^ 2 := Nat.floor_le (by positivity)
    push_cast
    linarith
  have hretain := Kernel.eventually_pow_restrictNoise_ge ν step
    (fun _ => killedMarkedStep_measurable _ _ _) measurable_snd htail hscale hα hp hlen
  have hretainEnd := Kernel.eventually_pow_restrictNoise_ge ν step
    (fun _ => killedMarkedStep_measurable _ _ _) measurable_snd htail hscale hα hpEnd hlen
  have hpos : ∀ᶠ n in atTop, 0 < block n :=
    (Asymptotics.tendsto_diffusiveBlockLength_atTop_of_tendsto_atTop
      hscale hTpos).eventually_gt_atTop 0
  let q := -d₀ * T / w ^ 2 - Real.log 4
  let qEnd := -d₀ * 2 * T / w ^ 2 - Real.log 4
  have hqexp : Real.exp q = p / 2 := by
    dsimp [q, p]; rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; ring
  have hqEndexp : Real.exp qEnd = pEnd / 2 := by
    dsimp [qEnd, pEnd]; rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; ring
  have hqbudget : -d < q / T := by
    have hb := (div_lt_iff₀ hgap).1 hlarge
    apply (lt_div_iff₀ hTpos).2
    dsimp [q]
    have heq : -d₀ * T / w ^ 2 = -(d₀ / w ^ 2) * T := by ring
    rw [heq]; nlinarith only [hb]
  have hlenRatio := Asymptotics.tendsto_floorBlockLength_div_sq_of_tendsto_atTop hscale hTpos
  have hcount := Asymptotics.tendsto_succ_quotientBlockCount_mul_scale_div
    (horizon := horizon) (scale := fun n => scale n ^ 2)
    (Eventually.of_forall (fun n => sq_nonneg (scale n))) hpos horizonPos hlenRatio hTpos hsmall
  have hnormalized : Tendsto (fun n =>
      (q * ((horizon n / block n + 1 : ℕ) : ℝ) + Real.log 4) *
        scale n ^ 2 / (horizon n : ℝ)) atTop (𝓝 (q / T)) := by
    have h := (hcount.const_mul q).add (hsmall.const_mul (Real.log 4))
    simpa only [mul_add, add_mul, add_div, mul_one_div, mul_div_assoc, mul_assoc, mul_zero, add_zero, block] using h
  have hsmallBlock : Tendsto (fun n => (block n : ℝ) / (horizon n : ℝ)) atTop (𝓝 0) := by
    have h := hlenRatio.mul hsmall
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    change ((block n : ℝ) / scale n ^ 2) * (scale n ^ 2 / (horizon n : ℝ)) = _
    field_simp
  have hcost := hnormalized.eventually (Ioi_mem_nhds hqbudget)
  filter_upwards [hi, hr, hf, hretain, hretainEnd, hpos, hcost, horizonPos,
    hscale.eventually_gt_atTop 0, hsmallBlock.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))]
    with n hentryN hreturnN hendN hret hretEnd hblock hcostN hH hL hshort
  have htwo : 2 ≤ horizon n / block n := by
    apply (Nat.le_div_iff_mul_le hblock).2
    have hshort' := (div_lt_iff₀ (show (0 : ℝ) < horizon n by exact_mod_cast hH)).1 hshort
    exact_mod_cast (show (2 : ℝ) * block n ≤ horizon n by linarith)
  let repeats := horizon n / block n - 2
  let finalLength := block n + horizon n % block n
  have hfinalMin : block n ≤ finalLength := Nat.le_add_right _ _
  have hfinalMax : finalLength ≤ 2 * block n := by
    have hm := Nat.mod_lt (horizon n) hblock
    dsimp [finalLength]; omega
  have hdecomp : block n + repeats * block n + finalLength = horizon n := by
    dsimp [repeats, finalLength]
    calc
      _ = (horizon n / block n - 2 + 2) * block n + horizon n % block n := by ring
      _ = horizon n / block n * block n + horizon n % block n := by rw [Nat.sub_add_cancel htwo]
      _ = horizon n := by simpa only [Nat.mul_comm] using Nat.div_add_mod (horizon n) (block n)
  have hin : ENNReal.ofReal (p / 2) ≤ (K n ^ block n) (a * scale n) (core n) := by
    apply hret (block n) (by omega) (a * scale n) (core n) measurableSet_Icc
    have hx : a * scale n ∈ Set.Icc ((a - 3 * e) * scale n) ((a + 3 * e) * scale n) := by
      constructor <;> nlinarith only [mul_pos he hL]
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hentryN _ le_rfl (by simp) _ hx)
    simpa only [ENNReal.toReal_ofReal hp.le] using h
  have hmid : ∀ x ∈ core n, ENNReal.ofReal (p / 2) ≤ (K n ^ block n) x (core n) := by
    intro x hx
    apply hret (block n) (by omega) x (core n) measurableSet_Icc
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hreturnN _ le_rfl (by simp) _ hx)
    simpa only [ENNReal.toReal_ofReal hp.le] using h
  have hout : ∀ x ∈ core n, ENNReal.ofReal (pEnd / 2) ≤ (K n ^ finalLength) x (lastCore n) := by
    intro x hx
    apply hretEnd finalLength hfinalMax x (lastCore n) measurableSet_Icc
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hendN _ hfinalMin hfinalMax _ hx)
    simpa only [ENNReal.toReal_ofReal hpEnd.le] using h
  have hprod := Kernel.mul_pow_mul_le_pow_of_returnKernel (K n) (core n) (lastCore n)
    measurableSet_Icc measurableSet_Icc (block n) (block n) repeats finalLength (a * scale n)
    _ _ _ hin hmid hout
  rw [hdecomp] at hprod
  rw [← hqexp, ← hqEndexp] at hprod
  have hcostEq : q * ((horizon n / block n + 1 : ℕ) : ℝ) + Real.log 4 =
      q + (repeats : ℝ) * q + qEnd := by
    have hnat : repeats + 3 = horizon n / block n + 1 := by dsimp [repeats]; omega
    have hcast : (repeats : ℝ) + 3 = ((horizon n / block n + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [← hcast]
    dsimp [q, qEnd]
    ring
  have hfac : -d * (horizon n : ℝ) / scale n ^ 2 ≤
      q * ((horizon n / block n + 1 : ℕ) : ℝ) + Real.log 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hL)).2
    have hh := (lt_div_iff₀ (show (0 : ℝ) < horizon n by exact_mod_cast hH)).1 hcostN
    linarith
  have hexp : ENNReal.ofReal (Real.exp (q * ((horizon n / block n + 1 : ℕ) : ℝ) + Real.log 4)) =
      ENNReal.ofReal (Real.exp q) * ENNReal.ofReal (Real.exp q) ^ repeats *
        ENNReal.ofReal (Real.exp qEnd) := by
    rw [hcostEq, Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg q) (pow_nonneg (Real.exp_nonneg q) repeats)),
      ENNReal.ofReal_mul (Real.exp_nonneg q), ENNReal.ofReal_pow (Real.exp_nonneg q)]
  refine ((ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hfac)).trans (hexp.le.trans hprod)).trans ?_
  have htarget : lastCore n ⊆ Set.Icc ((b - ρ) * scale n) ((b + ρ) * scale n) := by
    intro x hx
    have hm := mul_le_mul_of_nonneg_right hρw.le hL.le
    change (3 * e) * scale n ≤ ρ * scale n at hm
    constructor <;> nlinarith only [hx.1, hx.2, hm]
  refine (measure_mono htarget).trans_eq ?_
  rw [Kernel.pow_apply_ofPartialStep_eq_iidSequenceLaw ν _ _ measurableSet_Icc]
  congr 1
  ext ω
  exact endsInPrefix_restrictNoise_killedMarkedStep_iff _ _ _ _ _ _ _ _

/-- Exponential endpoint payoffs on the marked corridor. This is the spinal
first-moment input in B. Mallein, *Necessary and sufficient conditions for
the convergence of the consistent maximal displacement of the branching
random walk*, proof of Lemma 3.4 (arXiv:1510.00602v2), derived from the
marked endpoint lower bound and the terminal constraint. -/
theorem eventually_lintegral_exp_affineCorridorEndpoint_ge_of_finiteVariance
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {sigma c α d a b ρ θ : ℝ}
    (hν : IsCenteredSecondMoment (ν.map Prod.fst) (sigma ^ 2))
    (hσ : 0 < sigma) (htail : HasVanishingQuadraticTail ν Prod.snd)
    (hc : 0 ≤ c) (hα : 0 < α)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ) (hθ : 0 ≤ θ)
    {scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    (hscale : Tendsto scale atTop atTop)
    (horizonPos : ∀ᶠ n in atTop, 0 < horizon n)
    (hsmall : Tendsto (fun n => scale n ^ 2 / (horizon n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (θ * ((b - ρ - a) * scale n + c * (horizon n : ℝ) / scale n ^ 2) -
        d * (horizon n : ℝ) / scale n ^ 2)) ≤
      ∫⁻ ω in corridorEndpointEvent (-(scale n / 2)) (scale n / 2)
          (c / scale n ^ 2) (α * scale n) (horizon n) (a * scale n)
          (Set.Icc ((b - ρ) * scale n) ((b + ρ) * scale n)),
        ENNReal.ofReal (Real.exp (θ * AdditivePath.displacement (horizon n) (fun j => (ω j).1)))
        ∂iidSequenceLaw ν := by
  have hbound := eventually_affineCorridorEndpointProbability_ge_exp_of_finiteVariance
    ν hν hσ htail hc hα hd ha ha' hb hb' hρ hscale horizonPos hsmall
  filter_upwards [hbound] with n hn
  let E := corridorEndpointEvent (-(scale n / 2)) (scale n / 2)
    (c / scale n ^ 2) (α * scale n) (horizon n) (a * scale n)
    (Set.Icc ((b - ρ) * scale n) ((b + ρ) * scale n))
  let lower := θ * ((b - ρ - a) * scale n + c * (horizon n : ℝ) / scale n ^ 2)
  have hpoint (ω : ℕ → ℝ × ℝ) (hω : ω ∈ E) :
      lower ≤ θ * AdditivePath.displacement (horizon n) (fun j => (ω j).1) := by
    have ht := hω.2.1
    have hsum : AdditivePath.displacement (horizon n) (fun j => (ω j).1 - c / scale n ^ 2) =
        AdditivePath.displacement (horizon n) (fun j => (ω j).1) -
          (horizon n : ℝ) * (c / scale n ^ 2) := by
      simp [AdditivePath.displacement, Finset.sum_sub_distrib]
    rw [hsum] at ht
    apply mul_le_mul_of_nonneg_left _ hθ
    rw [show c * (horizon n : ℝ) / scale n ^ 2 =
      (horizon n : ℝ) * (c / scale n ^ 2) by ring]
    nlinarith only [ht]
  calc
    _ = ENNReal.ofReal (Real.exp lower) *
        ENNReal.ofReal (Real.exp (-d * (horizon n : ℝ) / scale n ^ 2)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      dsimp [lower]
      ring
    _ ≤ ENNReal.ofReal (Real.exp lower) * iidSequenceLaw ν E := mul_le_mul' le_rfl hn
    _ = ∫⁻ _ in E, ENNReal.ofReal (Real.exp lower) ∂iidSequenceLaw ν := by
      rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono'
      (measurableSet_corridorEndpointEvent _ _ _ _ _ _ measurableSet_Icc)
      (fun ω hω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpoint ω hω)))

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
  have h := eventually_affineCorridorEndpointProbability_ge_exp_of_finiteVariance
    (a := 0) (b := 0) (ρ := 1) ν hν hσ htail hc hα hd
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hscale horizonPos hsmall
  filter_upwards [h] with n hn
  simpa only [zero_mul] using hn.trans
    (measure_mono (Set.inter_subset_left : corridorEndpointEvent _ _ _ _ _ _ _ ⊆ _))

end ProbabilityTheory.RandomWalk.SmallDeviation.Marked
