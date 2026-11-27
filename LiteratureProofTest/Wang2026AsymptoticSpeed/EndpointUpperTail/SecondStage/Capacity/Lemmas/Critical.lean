/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Capacity.Lemmas.MarkovDecomposition
import all LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Capacity.Lemmas.Tube.Probability
import all LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Capacity.Lemmas.Tube.Event
import all LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Lemmas.Parameters
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SecondStage.Population
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceUpper.Basic

/-!
# Population cap for the critical second-stage tube

## Internal proof declarations

* `measure_positiveASelectedBRW_capacityEvent_compl_le_of_criticalTube`:
  write $D=H-\ell$ and $w=cD^{1/3}$. With the critical drift coefficient
  $\kappa=\pi^2\sigma^2/2$, a uniform tilted-tube bound at rate
  $\kappa-s$ yields
  $\mathbb P(\exists j\le H,\#P_j>N)\le
  \frac{m}{N+1}\left(\ell+1+D e^{(-b+v)\log N+w+\sqrt w+sD/w^2}\right)$.

This is the first-moment bound in Chapter 4, Theorem 1.1, case $0<a<1$ of
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026). The prefix estimate uses the
same upper bound as Chapter 3, Lemma 3.7, equation (3.9).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace LiteratureProofTest.Wang2026AsymptoticSpeed

open ProbabilityTheory
open ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open Asymptotics

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

private lemma sum_fin_if_le_eq_add_mul (ell ellN : ℕ) (A B : ℝ≥0∞)
    (hell : ell ≤ ellN) :
    (∑ k : Fin (ellN + 1), if (k : ℕ) ≤ ell then A else B) =
      ((ell + 1 : ℕ) : ℝ≥0∞) * A +
        ((ellN - ell : ℕ) : ℝ≥0∞) * B := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k ≤ ell then A else B)]
  rw [← Finset.sum_range_add_sum_Ico
    (fun k : ℕ => if k ≤ ell then A else B)
    (show ell + 1 ≤ ellN + 1 by omega)]
  have hfirst :
      (∑ k ∈ Finset.range (ell + 1), if k ≤ ell then A else B) =
        ((ell + 1 : ℕ) : ℝ≥0∞) * A := by
    have hterm : ∀ k ∈ Finset.range (ell + 1), (if k ≤ ell then A else B) = A := by
      intro k hk
      have hk' : k < ell + 1 := Finset.mem_range.mp hk
      simp [Nat.lt_succ_iff.mp hk']
    rw [Finset.sum_congr rfl hterm]
    simp [Finset.sum_const]
  have hsecond :
      (∑ k ∈ Finset.Ico (ell + 1) (ellN + 1), if k ≤ ell then A else B) =
        ((ellN - ell : ℕ) : ℝ≥0∞) * B := by
    have hterm : ∀ k ∈ Finset.Ico (ell + 1) (ellN + 1),
        (if k ≤ ell then A else B) = B := by
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      simp [Nat.not_le_of_gt hk'.1]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlength : ellN + 1 - (ell + 1) = ellN - ell := by omega
    rw [hlength]
    simp [Finset.sum_const]
  rw [hfirst, hsecond]

lemma measure_positiveASelectedBRW_capacityEvent_compl_le_of_criticalTube
    (m ell H N : ℕ) (logN b v c κ s : ℝ)
    (hell : 0 < ell) (hellH : ell < H) (hb : 0 ≤ b) (hL : 0 ≤ logN)
    (hvb : v ≤ b) (hvc : v ≤ c) (hc : 0 < c) (hs : 0 ≤ s)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (htube : ∀ j : ℕ,
      let w := c * (((H - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
      let ν := tiltedIncrementFieldLaw realPotential μ
      ν (driftedTubeEvent j w κ 0) ≤
        ENNReal.ofReal (Real.exp (w ^ (1 / 2 : ℝ) - (κ - s) * ((j : ℝ) / w ^ 2)))) :
    let P := positiveASelectedBRWPopulation m ell H logN b v c κ
    let w := c * (((H - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
    (finiteRootStepFieldLaw μ m) (P.capacityEvent N H)ᶜ ≤
      (m : ℝ≥0∞) * (((ell + 1 : ℕ) : ℝ≥0∞) + ((H - ell : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp ((-b + v) * logN + w + w ^ (1 / 2 : ℝ) +
          s * ((H - ell : ℕ) : ℝ) / w ^ 2))) / (N + 1 : ℕ) := by
  classical
  let w := c * (((H - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  let ν := tiltedPotentialLaw realPotential (-1) μ
  let _ := tiltedPotentialLaw_isProbability realPotential μ hboundary
  have hν : tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν := rfl
  let p (k : ℕ) : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (w ^ (1 / 2 : ℝ) - (κ - s) * (((k - ell : ℕ) : ℝ) / w ^ 2)))
  let U := positiveAWindowUpper ell H logN b v c κ
  let E := (-b + v) * logN + w + w ^ (1 / 2 : ℝ) + s * ((H - ell : ℕ) : ℝ) / w ^ 2
  have hdrift (j : ℕ) : positiveADrift ell H κ c j = κ * (j : ℝ) / w ^ 2 := by
    exact positiveADrift_eq_rate ell H j κ c hellH hc
  have hfirst (k : Fin (H + 1)) (_hk : (k : ℕ) ≤ ell) :
      restartedWindowProbability (tiltedIncrementFieldLaw realPotential μ) ell
        (positiveARestartedWindow ell H logN b v c κ) (k : ℕ) 0 ≤ 1 := by
    rw [hν]
    exact prob_le_one
  have hsecond (k : Fin (H + 1)) (hk : ell < (k : ℕ)) :
      restartedWindowProbability (tiltedIncrementFieldLaw realPotential μ) ell
        (positiveARestartedWindow ell H logN b v c κ) (k : ℕ) 0 ≤ p k := by
    have hkH : (k : ℕ) ≤ H := Nat.le_of_lt_succ k.isLt
    have hd : (k : ℕ) - ell ≤ H - ell := Nat.sub_le_sub_right hkH _
    rw [hν]
    refine (iidSequenceLaw_restartedWindowProbability_le_secondStagePrefix ν
      ell H (k : ℕ) logN b v c κ hk hkH).trans ?_
    have hsub : positiveASecondStageTubePrefixEvent ell H ((k : ℕ) - ell) κ c v ⊆
        driftedTubeEvent ((k : ℕ) - ell) w κ 0 := by
      intro increments hin j hj₁ hj₂
      have hj := (positiveASecondStageTubePrefixEvent_subset_fixedTube ell H _
        κ c v hellH hd hc.le hvc hin) ⟨j, Nat.lt_succ_of_le hj₂⟩
      simpa only [hdrift, zero_add, Set.mem_Icc, w] using hj
    exact (measure_mono hsub).trans (hν ▸ htube ((k : ℕ) - ell))
  have hbound := measure_positiveASelectedBRW_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds
    m ell H N logN b v c κ hell hellH hb hL hvb μ hboundary (fun _ => 1) p hfirst hsecond
  have hsum :
      (∑ k : Fin (H + 1), if (k : ℕ) ≤ ell then 1 else
        ENNReal.ofReal (Real.exp (U ell + U k)) * p k) ≤
        (((ell + 1 : ℕ) : ℝ≥0∞) + ((H - ell : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp E)) := by
    calc
      _ ≤ ∑ k : Fin (H + 1), if (k : ℕ) ≤ ell then 1 else ENNReal.ofReal (Real.exp E) := by
        apply Finset.sum_le_sum
        intro k _
        by_cases hk : (k : ℕ) ≤ ell
        · simp [hk]
        have hkH : (k : ℕ) ≤ H := Nat.le_of_lt_succ k.isLt
        have hU := positiveAWindowUpper_le_generationDrift_add_width ell H (k : ℕ)
          logN b v c κ hellH hvc (Nat.lt_of_not_ge hk) hkH
        have hcut := positiveAWindowUpper_at_cutoff ell H logN b v c κ
        have he₁ : U ell = (-b + v) * logN := hcut
        have he₂ : U k ≤ κ * (((k : ℕ) - ell : ℕ) : ℝ) / w ^ 2 + w := by
          simpa only [hdrift, U, w] using hU
        have hmono : s * (((k : ℕ) - ell : ℕ) : ℝ) / w ^ 2 ≤
            s * ((H - ell : ℕ) : ℝ) / w ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le_sub_right hkH ell) hs) (sq_nonneg w)
        simp only [hk, p, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        rw [he₁]
        dsimp [E]
        ring_nf at he₂ hmono ⊢
        linarith
      _ = _ := by rw [sum_fin_if_le_eq_add_mul ell H _ _ hellH.le, mul_one]
  exact hbound.trans (ENNReal.div_le_div_right (mul_le_mul_of_nonneg_left hsum (by positivity)) _)

end LiteratureProofTest.Wang2026AsymptoticSpeed
