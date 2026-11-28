/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.Law
public import MeasureTheory.Measure.Tails.Quadratic
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weak reproductive tails under the original spinal measure

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.HasFiniteCrossWeight.hasSpinalWeightTail`:
  `∫C dμ<∞`, `∫W dμ=1` and finite spinal second moment imply
  `x² μ̂{log W+X>x}→0`. No centering or nonzero variance is needed.

In `ProbabilityTheory.BranchingRandomWalk`:

* `relativeSpinalWeight φ (ξ,i)` is `log W(ξ) + φ(ξᵢ)`.
* `relativeSpinalWeight_measurable` gives measurability of the relative mark.
* `relativeSpinalWeight_nonneg` proves `log W + X ≥ 0` at a finite-weight surviving slot;
  `ae_relativeSpinalWeight_nonneg` gives this almost surely under the spinal law.
* `HasSpinalWeightTail φ μ` means `x² μ̂{log W + X > x} → 0`.
* `hasSpinalWeightTail_iff_totalWeightTail` proves that this is equivalent to
  `x² (μ.withDensity W){log W > x} → 0` under boundary normalization and
  finite spinal second moment. No logarithmic second moment is assumed.

The deterministic `logTotalPotentialWeight` observation is imported from
`Combinatorics/BranchingWalk/Step/Measure/ExponentialWeight.lean`.
Here `μ̂ = Spine.tiltedFamilyChildLaw φ (-1) μ` is the existing joint family/child
bias and `X = φ(ξᵢ)` has the original scalar law `Spine.tiltedPotentialLaw`.
This is condition (1.9) in B. Mallein, *N-branching random walk with α-stable
spine* (2015), Theorem 1.1, arXiv:1503.03762, reflected to leftmost selection
and specialized to finite variance. The total-weight version is condition (1.4)
in B. Mallein, *Necessary and sufficient conditions for the convergence of the
consistent maximal displacement of the branching random walk*, arXiv:1510.00602v2.

The real logarithm is totalized using `ENNReal.toReal`; under boundary
normalization the infinite-weight set is null. The zero-weight set has zero
spinal measure. Dependence between the displacement and the family weight is
retained throughout, and no independence premise is introduced.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk
open MeasureTheory Combinatorics.Branching
open Spine
open scoped ENNReal Classical

variable {ι X : Type*} [Countable ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace X]

/-- Relative exponential family weight seen from the distinguished child. -/
noncomputable def relativeSpinalWeight (φ : Potential X) (p : Step ι X × ι) : ℝ :=
  logTotalPotentialWeight φ p.1 + p.1.potentialValue' φ p.2

theorem relativeSpinalWeight_measurable (φ : Potential X) :
    Measurable (relativeSpinalWeight (ι := ι) φ) :=
  ((logTotalPotentialWeight_measurable φ).comp measurable_fst).add
    (measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i))

omit [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- The selected child's own positive weight is one summand of the total;
the relative reproductive mark is therefore nonnegative at every finite-weight
family with that child present. -/
theorem relativeSpinalWeight_nonneg (φ : Potential X) (p : Step ι X × ι)
    (hfinite : totalPotentialWeight φ (-1) p.1 ≠ ∞) (hs : survive p.1 p.2) :
    0 ≤ relativeSpinalWeight φ p := by
  have hw : ENNReal.ofReal (Real.exp (-p.1.potentialValue' φ p.2)) ≤
      totalPotentialWeight φ (-1) p.1 := by
    simpa only [totalPotentialWeight, realizedPotentialWeight, hs, ↓reduceIte, neg_one_mul] using
      (le_tsum (realizedPotentialWeight φ (-1) p.1) p.2)
  have hr : Real.exp (-p.1.potentialValue' φ p.2) ≤
      (totalPotentialWeight φ (-1) p.1).toReal := by
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using ENNReal.toReal_mono hfinite hw
  have hp : 0 < (totalPotentialWeight φ (-1) p.1).toReal :=
    (Real.exp_pos _).trans_le hr
  have hl := (Real.le_log_iff_exp_le hp).mpr hr
  change 0 ≤ Real.log (totalPotentialWeight φ (-1) p.1).toReal +
    p.1.potentialValue' φ p.2
  linarith

theorem ae_relativeSpinalWeight_nonneg (φ : Potential X) (μ : Measure (Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    ∀ᵐ p ∂tiltedFamilyChildLaw φ (-1) μ, 0 ≤ relativeSpinalWeight φ p := by
  have hraw : ∀ᵐ ξ ∂μ.withDensity (totalPotentialWeight φ (-1)),
      totalPotentialWeight φ (-1) ξ ≠ ∞ :=
    (hboundary.ae_totalPotentialWeight_ne_top φ μ).filter_mono
      (Measure.ae_le_iff_absolutelyContinuous.mpr (withDensity_absolutelyContinuous μ _))
  have hmap : ∀ᵐ ξ ∂(tiltedFamilyChildLaw φ (-1) μ).map Prod.fst,
      totalPotentialWeight φ (-1) ξ ≠ ∞ := by
    rw [tiltedFamilyChildLaw_fst]
    exact hraw
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hmap,
    ae_tiltedFamilyChildLaw_survive φ (-1) μ] with p hp hs
  exact relativeSpinalWeight_nonneg φ p hp hs

/-- Mallein's weak tail condition on the relative reproductive mark. -/
def HasSpinalWeightTail (φ : Potential X) (μ : Measure (Step ι X)) : Prop :=
  HasVanishingQuadraticTail (tiltedFamilyChildLaw φ (-1) μ) (relativeSpinalWeight φ)

/-- Finite spinal variance makes the relative-mark and total-log-weight
conditions equivalent, by two half-threshold union bounds.
This compares Mallein (2015), arXiv:1503.03762, condition (1.9), with
Mallein, arXiv:1510.00602v2, condition (1.4), in the finite-variance case. -/
theorem hasSpinalWeightTail_iff_totalWeightTail
    (φ : Potential X) (μ : Measure (Step ι X))
    (hboundary : HasBoundaryNormalization φ μ)
    (hsq : Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw φ (-1) μ)) :
    HasSpinalWeightTail φ μ ↔
      HasVanishingQuadraticTail (μ.withDensity (totalPotentialWeight φ (-1)))
        (logTotalPotentialWeight φ) := by
  let P := tiltedFamilyChildLaw φ (-1) μ
  have : IsProbabilityMeasure P := tiltedFamilyChildLaw_isProbability φ μ hboundary
  have hX : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  have hsq' : Integrable (fun p : Step ι X × ι => (p.1.potentialValue' φ p.2) ^ 2) P := by
    have hi : Integrable (fun x : ℝ => x ^ 2) (P.map
        (fun p => p.1.potentialValue' φ p.2)) := by
      simpa only [P, tiltedFamilyChildLaw_map_potential] using hsq
    exact hi.comp_measurable hX
  have he := hasVanishingQuadraticTail_add_iff_of_integrable_sq
    (f := fun p : Step ι X × ι => logTotalPotentialWeight φ p.1) hX hsq'
  have hf := hasVanishingQuadraticTail_map_iff (μ := P)
    Prod.fst measurable_fst (logTotalPotentialWeight φ)
    (logTotalPotentialWeight_measurable φ)
  rw [show P.map Prod.fst = μ.withDensity (totalPotentialWeight φ (-1)) from
    tiltedFamilyChildLaw_fst φ (-1) μ] at hf
  exact he.trans hf.symm

omit [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
private lemma relativeSpinalWeight_sq_le_otherWeight
    (φ : Potential X) (ξ : Step ι X) (i : ι)
    (hO : (∑' j : ι, if j ≠ i then realizedPotentialWeight φ (-1) ξ j else 0) ≠ ∞)
    (hs : survive ξ i) :
    relativeSpinalWeight φ (ξ, i) ^ 2 ≤ 8 * (ξ.potentialValue' φ i) ^ 2 +
      8 * (1 + (∑' j : ι, if j ≠ i then realizedPotentialWeight φ (-1) ξ j else 0).toReal) := by
  classical
  let O := ∑' j : ι, if j ≠ i then realizedPotentialWeight φ (-1) ξ j else 0
  let x := ξ.potentialValue' φ i
  let o := O.toReal
  let g := Real.log (1 + o)
  have hwi : realizedPotentialWeight φ (-1) ξ i ≠ ∞ := by
    unfold realizedPotentialWeight
    split <;> finiteness
  have hW : totalPotentialWeight φ (-1) ξ = realizedPotentialWeight φ (-1) ξ i + O := by
    calc
      _ = realizedPotentialWeight φ (-1) ξ i +
          ∑' j, if j = i then 0 else realizedPotentialWeight φ (-1) ξ j :=
        by simpa only [totalPotentialWeight] using
          (tsum_eq_add_tsum_ite (f := fun j => realizedPotentialWeight φ (-1) ξ j) i)
      _ = _ := by
        congr 1
        apply tsum_congr
        intro j
        by_cases hj : j = i <;> simp [hj]
  have hWfinite : totalPotentialWeight φ (-1) ξ ≠ ∞ := by
    rw [hW]
    exact ENNReal.add_ne_top.mpr ⟨hwi, hO⟩
  have hWeq : (totalPotentialWeight φ (-1) ξ).toReal = Real.exp (-x) + o := by
    rw [hW, ENNReal.toReal_add hwi hO]
    change (realizedPotentialWeight φ (-1) ξ i).toReal + o = _
    rw [show realizedPotentialWeight φ (-1) ξ i = ENNReal.ofReal (Real.exp (-x)) by
      simp [realizedPotentialWeight, hs, x], ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have ho : 0 ≤ o := ENNReal.toReal_nonneg
  have hg : 0 ≤ g := Real.log_nonneg (by linarith)
  have hWpos : 0 < (totalPotentialWeight φ (-1) ξ).toReal := by
    rw [hWeq]
    positivity
  have hexp : 1 ≤ Real.exp |x| := Real.one_le_exp_iff.mpr (abs_nonneg x)
  have hWle : (totalPotentialWeight φ (-1) ξ).toReal ≤ Real.exp |x| * (1 + o) := by
    rw [hWeq]
    have hx := Real.exp_le_exp.mpr (neg_le_abs x)
    have ho' : o ≤ Real.exp |x| * o := by nlinarith only [hexp, ho]
    nlinarith only [hx, ho']
  have hlog : Real.log (totalPotentialWeight φ (-1) ξ).toReal ≤ |x| + g := by
    have h := Real.log_le_log hWpos hWle
    rwa [Real.log_mul (Real.exp_ne_zero _) (by positivity : (1 + o : ℝ) ≠ 0), Real.log_exp] at h
  have hM : relativeSpinalWeight φ (ξ, i) ≤ 2 * |x| + g := by
    change Real.log (totalPotentialWeight φ (-1) ξ).toReal + x ≤ _
    linarith [le_abs_self x]
  have hMpos := relativeSpinalWeight_nonneg φ (ξ, i) hWfinite hs
  have hR : 0 ≤ (1 + o) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hR2 : ((1 + o) ^ (1 / 2 : ℝ)) ^ 2 = 1 + o := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hgR : g ≤ 2 * (1 + o) ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 + o)
      (by norm_num : (0 : ℝ) < 1 / 2)
    dsimp [g]
    linarith
  have hg2 : g ^ 2 ≤ 4 * (1 + o) := by
    have h := pow_le_pow_left₀ hg hgR 2
    nlinarith only [h, hR2]
  have hM2 := pow_le_pow_left₀ hMpos hM 2
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  change _ ≤ 8 * x ^ 2 + 8 * (1 + o)
  nlinarith [sq_nonneg (2 * |x| - g)]

/-- A finite cross-child weight implies Mallein's weak reproductive tail
when the scalar spine has finite second moment. The proof bounds the squared
relative mark by the spinal squared displacement and the other-child weight.
This compares Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1,
with condition (1.9) of B. Mallein, *N-branching random walk with α-stable
spine*, arXiv:1503.03762v2. -/
theorem HasFiniteCrossWeight.hasSpinalWeightTail
    (φ : Potential X) (μ : Measure (Step ι X))
    (hcross : HasFiniteCrossWeight φ μ) (hboundary : HasBoundaryNormalization φ μ)
    (hsq : Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw φ (-1) μ)) :
    HasSpinalWeightTail φ μ := by
  classical
  let P := tiltedFamilyChildLaw φ (-1) μ
  let : IsProbabilityMeasure P := tiltedFamilyChildLaw_isProbability φ μ hboundary
  let O := fun p : Step ι X × ι => ∑' j : ι,
    if j ≠ p.2 then realizedPotentialWeight φ (-1) p.1 j else 0
  have hOm : Measurable O := by
    apply Measurable.tsum
    intro j
    exact Measurable.ite (by
      convert (measurable_snd (measurableSet_singleton j)).compl using 1
      ext p
      simp [ne_comm])
      ((realizedPotentialWeight_measurable φ (-1) j).comp measurable_fst) measurable_const
  have hOi : (∫⁻ p, O p ∂P) ≠ ∞ := by
    rw [lintegral_tiltedFamilyChildLaw_otherWeight φ (-1) μ]
    exact hcross
  have hOae : ∀ᵐ p ∂P, O p ≠ ∞ := (ae_lt_top hOm hOi).mono fun _ hp => hp.ne
  have hOr : Integrable (fun p => (O p).toReal) P :=
    (integrable_toReal_iff hOm.aemeasurable hOae).2 hOi
  have hX : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  have hXs : Integrable (fun p : Step ι X × ι => (p.1.potentialValue' φ p.2) ^ 2) P := by
    have h : Integrable (fun x : ℝ => x ^ 2) (P.map (fun p => p.1.potentialValue' φ p.2)) := by
      simpa only [P, tiltedFamilyChildLaw_map_potential] using hsq
    exact h.comp_measurable hX
  have hbound : Integrable (fun p : Step ι X × ι =>
      8 * (p.1.potentialValue' φ p.2) ^ 2 + 8 * (1 + (O p).toReal)) P :=
    (hXs.const_mul 8).add (((integrable_const 1).add hOr).const_mul 8)
  have hM := relativeSpinalWeight_measurable (ι := ι) φ
  have hMsq : Integrable (fun p => relativeSpinalWeight φ p ^ 2) P := by
    apply hbound.mono' (hM.pow_const 2).aestronglyMeasurable
    filter_upwards [hOae, ae_tiltedFamilyChildLaw_survive φ (-1) μ] with p hp hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact relativeSpinalWeight_sq_le_otherWeight φ p.1 p.2 hp hs
  exact (hasVanishingQuadraticTail_abs_of_integrable_sq hM hMsq).mono (fun _ => le_abs_self _)

end ProbabilityTheory.BranchingRandomWalk
