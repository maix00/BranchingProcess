/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Basic
public import Probability.BranchingRandomWalk.Assumptions.SpinalWeightTail
public import Probability.Distributions.Moments.Real
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Overflow
import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.FamilySelection
import Probability.BranchingRandomWalk.Population.Processes.Causal.Path.Survival
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.FamilySelection

/-!
# Quantitative endpoint upper tails under the weak spinal reproductive tail

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_measure_endpointMinimum_gt_le_affineBudget_of_spinalWeightTail`:
  let `Lₙ→∞`, `Hₙ/Lₙ³→t>0`, `κ=π²σ²/2`, and
  `0<dUpper<κ<dLower`, `c≥dUpper`, `α,ρ>0`, `a,b∈(-1/2,1/2)`.
  For `β>α+4ρ+a+1/2+2(dLower-dUpper)t`, put
  `lowerₙ=-(a+1/2)Lₙ` and `Uₙ=(b+ρ-a)Lₙ+cHₙ/Lₙ²`.
  From `mₙ` zero-position roots with capacity `Nₙ>0`, the original first-`N`
  endpoint minimum satisfies eventually
  `P(Mₙ>Uₙ) ≤ exp(-mₙ exp(-βLₙ))`
  `+mₙ(Hₙ+1)exp(lowerₙ+Lₙ+√Lₙ+max(c-dUpper,0)Hₙ/Lₙ²)/(Nₙ+1)`.
  The original offspring law is boundary-normalized with centered finite
  spinal variance and Mallein's weak spinal weight tail. There is no finite
  cross-weight or logarithmic second-moment hypothesis.

The cutoff is used only to prove the original single-root success bound.
The actual original-law causal population, independent-root avoidance,
capacity inequality and stopped endpoint comparison are all existing
interfaces. No new population, coupling or endpoint observable is defined.
This combines the cutoff moments of B. Mallein, *N-branching random walk with
α-stable spine*, proof of Lemma 3.4, and independent-root amplification in
Lemma 4.8 (arXiv:1503.03762v2), with the capacity comparison of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 3, Lemma 3.15, and Chapter 4, proof of
Theorem 1.1, in the reflected spatial convention.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Filter MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

/-- Independent-root success and finite-root capacity control give the original
first-`N` endpoint upper tail under the weak reproductive assumption. See
B. Mallein, *N-branching random walk with α-stable spine*, proofs of Lemmas 3.4
and 4.8 (arXiv:1503.03762v2), and Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.15, and Chapter 4, proof of Theorem 1.1. -/
theorem eventually_measure_endpointMinimum_gt_le_affineBudget_of_spinalWeightTail
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    {σ c α dUpper dLower a b ρ t β : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (σ ^ 2))
    (hσ : 0 < σ) (htail : HasSpinalWeightTail realPotential μ) (hα : 0 < α)
    (hdUpper : 0 < dUpper) (hUpperCritical : dUpper < (Real.pi ^ 2 / 2) * σ ^ 2)
    (hLowerCritical : (Real.pi ^ 2 / 2) * σ ^ 2 < dLower) (hc : dUpper ≤ c)
    (ha : -(1 / 2 : ℝ) < a) (ha' : a < 1 / 2)
    (hb : -(1 / 2 : ℝ) < b) (hb' : b < 1 / 2) (hρ : 0 < ρ) (ht : 0 < t)
    (hβ : α + 4 * ρ + a + 1 / 2 + 2 * (dLower - dUpper) * t < β)
    {L : ℕ → ℝ} {H m N : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / L n ^ 3) atTop (𝓝 t))
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (m n)) ℕ)) :
    ∀ᶠ n in atTop,
      letI := horder n
      let lower := -(a + 1 / 2) * L n
      let U := (b + ρ - a) * L n + c * (H n : ℝ) / L n ^ 2
      finiteRootStepFieldLaw μ (m n)
        {field | U < firstNSelectedEndpointMinimum (m n) (N n) (H n) field} ≤
        ENNReal.ofReal (Real.exp (-(m n : ℝ) * Real.exp (-β * L n))) +
        (m n : ℝ≥0∞) * ((H n : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp
          (lower + L n + L n ^ (1 / 2 : ℝ) + max (c - dUpper) 0 * (H n : ℝ) / L n ^ 2)) /
          (N n + 1 : ℕ) := by
  have hsuccess := eventually_exp_le_measure_hasPathHistoryIn_affineCorridor_of_cubicScale
    realPotential μ hboundary hcentered hσ htail hα hdUpper hUpperCritical hLowerCritical hc
    ha ha' hb hb' hρ ht hβ hL hH
  obtain ⟨L₀, _, hcapacity⟩ :=
    RootIndexed.CausalPopulation.exists_measure_capacityEvent_compl_affine_selectFamily_le_exp_of_finiteVariance
      realPotential μ hboundary hcentered (sq_pos_of_pos hσ) (hdUpper.le.trans hc) hdUpper hUpperCritical
  filter_upwards [hsuccess, hL.eventually_ge_atTop L₀, hL.eventually_gt_atTop 0, hN]
    with n hsuc hlarge hpos hNn
  let := horder n
  dsimp only
  let lower := -(a + 1 / 2) * L n
  let U := (b + ρ - a) * L n + c * (H n : ℝ) / L n ^ 2
  let window := fun j : ℕ => Set.Icc (lower + c / L n ^ 2 * (j : ℝ))
    (lower + c / L n ^ 2 * (j : ℝ) + L n)
  let upper := fun j : ℕ => lower + c / L n ^ 2 * (j : ℝ) + L n
  let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin (m n) => (0 : ℝ)) id measurable_id
    (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin (m n))))
    (by simp [RootIndexed.mem_initialPopulation_iff]) 0 window (fun _ => measurableSet_Icc)
    upper (fun _ _ h => h.2)
  let slices := RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
    (fun _ : Fin (m n) => (0 : ℝ)) id measurable_id
    (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin (m n))))
    (by simp [RootIndexed.mem_initialPopulation_iff]) 0 window (fun _ => measurableSet_Icc)
    upper (fun _ _ h => h.2)
  let C := affineCorridorThrough (H n) lower (c / L n ^ 2) (L n) U
  have hprob : Real.exp (-β * L n) ≤
      (ProbabilityTheory.BranchingProcess.offspringFieldLaw μ).real
        (hasPathHistoryIn (ι := ℕ) realPotential (H n) 0 C) := by
    simpa only [C, lower, U, measureReal_def, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      ENNReal.toReal_mono (measure_ne_top _ _) hsuc
  have havoid := RootIndexed.CausalPopulation.measure_terminalPosition_avoidance_le_exp_of_pathSuccess
    realPotential μ (hboundary.ae_totalPotentialWeight_ne_top realPotential μ)
    (m n) (H n) 0 window (fun _ => measurableSet_Icc) upper (fun _ _ h => h.2)
    C (measurableSet_affineCorridorThrough _ _ _ _ _)
    (fun path hp hz k => by simpa [restartAnchor, hz, window] using hp.1 k)
    (Set.Iic U) (fun _ hp => hp.2) (Real.exp (-β * L n)) (Real.exp_nonneg _)
    (hprob.trans measureReal_le_one) hprob
  have hlower : -(L n) ≤ lower := by
    dsimp [lower]
    nlinarith only [mul_le_mul_of_nonneg_right ha'.le hpos.le]
  have hupper : lower ≤ 0 := by
    dsimp [lower]
    nlinarith only [mul_le_mul_of_nonneg_right ha.le hpos.le]
  have hcap := hcapacity (L n) hlarge Set.univ MeasurableSet.univ lower hlower hupper
    (Finset.univ : Finset (Fin (m n))) (fun _ => 0) (N n) (H n)
  dsimp only at hcap
  have hselect : Step.selectFamily (Set.univ : Set (Step ℕ ℝ)) = id := by
    funext ξ
    exact Step.selectFamily_of_mem (Set.mem_univ ξ)
  rw [hselect, Measure.map_id] at hcap
  simp only [Finset.card_univ, Fintype.card_fin] at hcap
  have hinit : ∀ field, Order.DominatingMap
      (↑(slices.toFinset 0 field) : Set (RootIndexed.TreeNode (Fin (m n)) ℕ))
      (↑(RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin (m n)))) :
        Set (RootIndexed.TreeNode (Fin (m n)) ℕ)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) := by
    intro field
    refine ⟨id, ?_, fun _ _ _ _ h => h, fun _ _ => le_rfl⟩
    intro p hp
    have hp' := (slices.mem_toFinset 0 field p).1 hp
    exact hp'
  have hcompare := RootIndexed.measure_endpointMinimum_gt_le_terminalAvoidance_add_capacityFailure
    μ (N n) hNn (Finset.univ : Finset (Fin (m n))) (fun _ => 0)
    hboundary.ae_isLeftLocallyFinite P slices hinit (H n) U
  have hreal : finiteRootStepFieldLaw μ (m n)
      {field | U < firstNSelectedEndpointMinimum (m n) (N n) (H n) field} ≤
      finiteRootStepFieldLaw μ (m n) {field | (U : WithTop ℝ) <
        (RootIndexed.selectedPopulationTotalized (N n) Finset.univ (fun _ : Fin (m n) => 0)
          id id (H n) field).inf (fun p =>
            ((RootIndexed.position (fun _ : Fin (m n) => 0) id field p.1 p.2 : ℝ) : WithTop ℝ))} := by
    apply measure_mono
    intro field hf
    apply (show (U : WithTop ℝ) < (firstNSelectedEndpointMinimum (m n) (N n) (H n) field : ℝ)
      from WithTop.coe_lt_coe.mpr hf).trans_le
    change _ ≤ (firstNSelectedPopulation (m n) (N n) (H n) field).inf _
    apply Finset.le_inf
    intro p hp
    rw [firstNSelectedEndpointMinimum_eq_inf'_of_nonempty _ _ _ field ⟨p, hp⟩]
    exact WithTop.coe_le_coe.mpr (Finset.inf'_le _ hp)
  have hdec : (fun a b : RootIndexed.TreeNode (Fin (m n)) ℕ =>
      LinearOrder.toDecidableEq a b) = (fun a b => instDecidableEqProd a b) := Subsingleton.elim _ _
  dsimp only at hcompare
  rw [hdec] at hcompare
  exact hreal.trans (hcompare.trans (add_le_add havoid hcap))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
