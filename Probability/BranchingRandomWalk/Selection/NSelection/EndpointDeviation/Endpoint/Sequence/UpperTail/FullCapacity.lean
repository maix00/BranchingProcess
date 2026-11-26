/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.UpperTail.PositiveInitialExponent
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Monotonicity

/-!
# Full-capacity endpoint upper tail under the weak reproductive condition

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_positiveExponent`:
  for `0<a≤1`, the weak-tail upper bound is `P(M_n≥ζ log N_n)≤N_n^(-p)`
  for each `ζ>-a+π²σ²t/2`, with nonempty offspring and the same normalization
  and variance assumptions. The full-capacity entry derives from this theorem.

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_fullCapacity`:
  under boundary normalization, nonempty offspring, the weak reproductive tail
  and centered spinal variance `σ²>0`, if `H_n/log³N_n→t>0` and
  `ζ>-1+π²σ²t/2`, then `P(M_(N_n,N_n)(H_n)≥ζ log N_n)≤N_n^(-p)`
  eventually for some `p>0`. No leftmost-child moment is required.

This is the root-monotonicity extension to `a=1` in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, proof of Theorem 1.1, with the
reproductive assumption weakened to B. Mallein, *N-branching random walk
with α-stable spine*, Theorem 1.1 condition (1.9), arXiv:1503.03762v2.
The subcapacity case is called directly, without a separate corridor proof.
-/

@[expose] public section
open Filter MeasureTheory
open scoped ENNReal Topology
namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

noncomputable local instance (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

/-- The `a=1` extension of Wang Yiyang, Chapter 4, Theorem 1.1, under
Mallein's weak reproductive condition (Theorem 1.1 (1.9), arXiv:1503.03762v2),
by comparison with `⌊N^b⌋` roots for `b<1` arbitrarily close to one. -/
private lemma fullCapacityUpperTail
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (htail : HasSpinalWeightTail realPotential μ)
    {sigma t ζ : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ht : 0 < t)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hgap : -1 + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ) {field | ζ * Real.log (N n : ℝ) ≤
        countableRootEndpointMinimum (N n) (N n) (H n) field} ≤
        ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  let P := RootIndexed.stepFieldLaw (Root := ℕ) μ
  let c := -1 + (Real.pi ^ 2 / 2) * sigma ^ 2 * t
  let ε := ζ - c
  have hε : 0 < ε := sub_pos.mpr hgap
  let d := min (1 / 2 : ℝ) (ε / 4)
  let b := 1 - d
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hb : 0 < b := by dsimp [b]; linarith [show d ≤ 1 / 2 from min_le_left _ _]
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hgapb : -b + Real.pi ^ 2 / 2 * sigma ^ 2 * t < c + ε / 2 := by
    dsimp [b, c]
    linarith [show d ≤ ε / 4 from min_le_right _ _]
  obtain ⟨p, hp, hupper⟩ :=
    eventually_countableRootEndpointMinimum_ge_le_polynomial_of_spinalWeightTail hN
      μ hboundary htail hsigma hspine hb hb1 ht hgapb hH
      (fun _ => inferInstance)
  refine ⟨p, hp, ?_⟩
  have hlog : Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  filter_upwards [hupper, hlog.eventually_gt_atTop 0, hN.eventually_gt_atTop 0] with n hup hlogn hcapacityN
  let m := Nat.floor ((N n : ℝ) ^ b)
  let x := (c + ε / 2) * Real.log (N n : ℝ)
  let y := (c + ε) * Real.log (N n : ℝ)
  let small := countableRootEndpointMinimum m (N n) (H n)
  let large := countableRootEndpointMinimum (N n) (N n) (H n)
  have hN1 : (1 : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hcapacityN
  have hm : 0 < m := Nat.floor_pos.mpr (Real.one_le_rpow hN1 hb.le)
  have hmN : m ≤ N n := by
    apply Nat.floor_le_of_le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hb1.le
  have hmono := measure_countableRootEndpointMinimum_le_mono_roots μ
    hboundary hnonempty hm hmN hcapacityN (H n) x
  have hsmall : MeasurableSet {field | small field ≤ x} :=
    (measurable_countableRootEndpointMinimum m (N n) (H n)) measurableSet_Iic
  have hlarge : MeasurableSet {field | large field ≤ x} :=
    (measurable_countableRootEndpointMinimum (N n) (N n) (H n)) measurableSet_Iic
  have hxy : x < y := mul_lt_mul_of_pos_right (by linarith) hlogn
  change P {field | ζ * Real.log (N n : ℝ) ≤ large field} ≤ _
  have hy : y = ζ * Real.log (N n : ℝ) := by dsimp [y, c, ε]; ring
  rw [← hy]
  calc
    _ ≤ P {field | large field ≤ x}ᶜ := by
      apply measure_mono
      intro field hf hle
      exact hxy.not_ge ((show y ≤ large field from hf).trans hle)
    _ ≤ P {field | small field ≤ x}ᶜ := by
      rw [prob_compl_eq_one_sub hlarge, prob_compl_eq_one_sub hsmall]
      exact tsub_le_tsub_left hmono _
    _ ≤ P {field | x ≤ small field} := by
      apply measure_mono
      intro field hf
      change x ≤ small field
      exact le_of_lt (lt_of_not_ge (show ¬ small field ≤ x from hf))
    _ ≤ _ := hup

/-- Under nonempty offspring, the positive-initial-exponent upper tail is
uniformly stated for the closed range `0<a≤1`. The open range calls the
original weak-tail corridor result; full capacity uses root monotonicity.
This is Wang Yiyang, Chapter 4, Theorem 1.1, with Mallein's condition (1.9)
(Theorem 1.1, arXiv:1503.03762v2). -/
theorem eventually_countableRootEndpointMinimum_ge_le_polynomial_of_positiveExponent
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (htail : HasSpinalWeightTail realPotential μ)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 0 < t)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ) {field | ζ * Real.log (N n : ℝ) ≤
        countableRootEndpointMinimum ⌊(N n : ℝ) ^ a⌋₊ (N n) (H n) field} ≤
        ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  by_cases hlt : a < 1
  · exact eventually_countableRootEndpointMinimum_ge_le_polynomial_of_spinalWeightTail
      hN μ hboundary htail hsigma hspine ha hlt ht hgap hH (fun _ => inferInstance)
  · have heq : a = 1 := le_antisymm ha1 (not_lt.mp hlt)
    have hgap1 : -1 + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ := by simpa only [heq] using hgap
    obtain ⟨p, hp, hbound⟩ := fullCapacityUpperTail hN μ hboundary hnonempty htail hsigma hspine ht hH hgap1
    refine ⟨p, hp, hbound.mono fun n hn => ?_⟩
    have hm : ⌊(N n : ℝ) ^ a⌋₊ = N n := by rw [heq, Real.rpow_one, Nat.floor_natCast]
    have hF : @countableRootEndpointMinimum ⌊(N n : ℝ) ^ a⌋₊ (N n) (H n)
        (RootIndexed.addressLinearOrder _ ℕ) =
        @countableRootEndpointMinimum (N n) (N n) (H n)
          (RootIndexed.addressLinearOrder _ ℕ) := by rw [hm]
    rw [hF]
    exact hn

/-- Full capacity specializes the common positive-exponent theorem; no
separate probability comparison is maintained. -/
theorem eventually_countableRootEndpointMinimum_ge_le_polynomial_of_fullCapacity
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1)
    (htail : HasSpinalWeightTail realPotential μ)
    {sigma t ζ : ℝ} (hsigma : 0 < sigma)
    (hspine : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ht : 0 < t)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hgap : -1 + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ) {field | ζ * Real.log (N n : ℝ) ≤
        countableRootEndpointMinimum (N n) (N n) (H n) field} ≤
        ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  obtain ⟨p, hp, h⟩ := eventually_countableRootEndpointMinimum_ge_le_polynomial_of_positiveExponent
    hN μ hboundary hnonempty htail hsigma hspine (a := 1) zero_lt_one le_rfl ht hH hgap
  refine ⟨p, hp, h.mono fun n hn => ?_⟩
  have hm : ⌊(N n : ℝ) ^ (1 : ℝ)⌋₊ = N n := by rw [Real.rpow_one, Nat.floor_natCast]
  have hF : @countableRootEndpointMinimum ⌊(N n : ℝ) ^ (1 : ℝ)⌋₊ (N n) (H n)
      (RootIndexed.addressLinearOrder _ ℕ) =
      @countableRootEndpointMinimum (N n) (N n) (H n)
        (RootIndexed.addressLinearOrder _ ℕ) := by rw [hm]
  rw [hF] at hn
  exact hn

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
