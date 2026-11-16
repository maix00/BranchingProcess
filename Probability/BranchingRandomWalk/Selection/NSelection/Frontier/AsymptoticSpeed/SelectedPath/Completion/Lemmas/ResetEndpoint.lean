/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Horizon
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.HorizonWindow

/-!
# Upper tail of the reset continuation at a successful entrance

## Internal proof declarations

* `eventually_measure_stoppedResetEndpoint_ge_le_polynomial`: for
  $m_N=\lfloor N^a\rfloor$, $0<a<1$, $H_N/\log^3 N\to t>0$,
  $T_N/\log^3 N\to0$ and $\zeta>-a+\pi^2\sigma^2t/2$,
  $\mathbb P(\tau_N\le T_N,M^{\mathrm{reset}}_{H_N-\tau_N}
  \ge\zeta\log N)\le N^{-p}$ eventually, for some $p>0$.

Translating all starting positions by the same real number adds that number
to the endpoint. The estimate applies the stopped branching product law
before testing the remaining horizon, as in Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1 for $a=0$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open ProbabilityTheory.BranchingRandomWalk.Spine

private lemma measure_stoppedResetEndpoint_ge_le
    {Root : Type*} (lower : ℕ) [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass (Root ⊕ Root)]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)]
    [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin lower) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin lower) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin lower) ℕ)]
    (hnodePath : Measurable
      (fun p : RootIndexed.TreeNode Root ℕ => p.2))
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (H T : ℕ) (x : ℝ) (b : ℝ≥0∞)
    (hbound : ∀ i ≤ T, RootIndexed.stepFieldLaw (Root := Fin lower) μ
      {f | x ≤ firstNSelectedEndpointMinimum lower N (H - i) f} ≤ b) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration r
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N {r} initialPosition trials τ hτ
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let roots := fun field (i : Fin lower) =>
      (r, (Completion.endpointNodesByRank N initialPosition R growth hR hgrowth
        lower upper duration r field i).2)
    P {field | ∃ i ≤ T, τ field = (i : WithTop ℕ) ∧
      x ≤ firstNSelectedEndpointMinimum lower N (H - i)
        (RootIndexed.subtreeStepFieldVector (roots field) (installed field))} ≤ b := by
  classical
  intro τ hτ trials installed P roots
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let E := {field | τ field ≠ ⊤}
  let data := fun field => (τ field, fun _ : Fin lower => (0 : ℝ))
  let outcome := fun field => (data field, RootIndexed.subtreeStepFieldVector (roots field) (installed field))
  let A : Set ((WithTop ℕ × (Fin lower → ℝ)) × (RootIndexed.StepField (Fin lower) ℕ ℝ)) :=
    {z | ∃ i ≤ T, z.1.1 = (i : WithTop ℕ) ∧
      x ≤ firstNSelectedEndpointMinimum lower N (H - i) z.2}
  have hA : MeasurableSet A := by
    rw [show A = ⋃ i : Fin (T + 1), {z | z.1.1 = ((i.val : ℕ) : WithTop ℕ) ∧
      x ≤ firstNSelectedEndpointMinimum lower N (H - i.val) z.2} by
        ext z
        simp only [A, Set.mem_ofPred_eq, Set.mem_iUnion, Fin.exists_iff]
        exact exists_congr fun i => by
          simp only [Nat.lt_succ_iff, exists_prop]]
    apply MeasurableSet.iUnion
    intro i
    exact ((measurable_fst.comp measurable_fst) (measurableSet_singleton _)).inter
      (((measurable_firstNSelectedEndpointMinimum lower N (H - i.val)).comp measurable_snd)
        measurableSet_Ici)
  obtain ⟨hmeas, hlaw⟩ := Completion.timePositionStoppedEntrance_jointLaw_on_finite
    lower hnodePath μ hnorm N initialPosition R growth hR hgrowth upper duration hupper
    hbounded hcapacity r (fun _ _ => 0) measurable_const
  change AEMeasurable outcome (P.restrict E) at hmeas
  change (P.restrict E).map outcome = ((P.restrict E).map data).prod Q at hlaw
  change P (outcome ⁻¹' A) ≤ b
  have hsubset : outcome ⁻¹' A ⊆ E := by
    rintro field ⟨i, _, hi, _⟩
    change τ field = (i : WithTop ℕ) at hi
    change τ field ≠ ⊤
    rw [hi]
    exact WithTop.coe_ne_top
  have hE : MeasurableSet E :=
    hτ.measurableSpace_le _ (hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ))).compl
  have hrestrict : (P.restrict E) (outcome ⁻¹' A) = P (outcome ⁻¹' A) := by
    rw [Measure.restrict_apply' hE, Set.inter_eq_left.mpr hsubset]
  rw [← hrestrict, ← Measure.map_apply_of_aemeasurable hmeas hA, hlaw, Measure.prod_apply hA]
  calc
    _ ≤ ∫⁻ _ , b ∂((P.restrict E).map data) := by
      apply lintegral_mono
      intro y
      by_cases hy : ∃ i ≤ T, y.1 = (i : WithTop ℕ)
      · obtain ⟨i, hi, htime⟩ := hy
        have hsec : (Prod.mk y) ⁻¹' A =
            {f | x ≤ firstNSelectedEndpointMinimum lower N (H - i) f} := by
          ext f
          constructor
          · rintro ⟨j, _, hj, hx⟩
            have hji : j = i := WithTop.coe_injective (hj.symm.trans htime)
            exact hji ▸ hx
          · exact fun hf => ⟨i, hi, htime, hf⟩
        simpa only [hsec] using hbound i hi
      · have hsec : (Prod.mk y) ⁻¹' A = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          rintro f ⟨i, hi, htime, _⟩
          exact hy ⟨i, hi, htime⟩
        simp [hsec]
    _ ≤ b := by
      rw [lintegral_const]
      have hmass : ((P.restrict E).map data) Set.univ ≤ 1 := by
        have hd : Measurable data := (hτ.measurable.mono hτ.measurableSpace_le le_rfl).prodMk
          measurable_const
        rw [Measure.map_apply hd MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
        calc
          P E ≤ P Set.univ := measure_mono (Set.subset_univ E)
          _ = 1 := measure_univ
      simpa using mul_le_mul_of_nonneg_left hmass (show 0 ≤ b from zero_le)

/-- Apply the positive-exponent estimate uniformly on the short stopping
window of the $a=0$ proof, for the zero-reset descendants of the ranked entrance. -/
lemma eventually_measure_stoppedResetEndpoint_ge_le_polynomial
    {Root : Type*} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass (Root ⊕ Root)]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)]
    [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root ℕ => p.2))
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {N H T : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0))
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ))
    (initialPosition : Root → ℝ) (r : Root)
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (growth : ℕ → Step.FiniteSelection ℕ ℝ) (hgrowth : ∀ n, Measurable (growth n).select)
    (upper duration : ℕ → ℕ)
    (htrials : ∀ᶠ n in atTop, 1 ≤ upper n ∧ (growth n).IsBoundedBy 2 ∧
      1 + (duration n + 1) * (2 * upper n) ≤ N n) :
    let lower := fun n => Nat.floor ((N n : ℝ) ^ a)
    let τ := fun n => Completion.time R (growth n) hR (hgrowth n)
      (lower n) (upper n) (duration n) r
    let hτ := fun n => Completion.time_isStoppingTime R (growth n) hR (hgrowth n)
      (lower n) (upper n) (duration n) r
    let trials := fun n => SelectedPath.Population.leftBRWFamily_finiteSlices R (growth n)
      hR (hgrowth n) (upper n) (duration n) r
    let installed := fun n => RootIndexed.stoppedRankInstalledTrajectoryField (N n) {r}
      initialPosition (trials n) (τ n) (hτ n)
    let roots := fun n field (i : Fin (lower n)) =>
      (r, (Completion.endpointNodesByRank (N n) initialPosition R (growth n) hR (hgrowth n)
        (lower n) (upper n) (duration n) r field i).2)
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      P {field | ∃ i ≤ T n, τ n field = (i : WithTop ℕ) ∧
        ζ * Real.log (N n : ℝ) ≤ @firstNSelectedEndpointMinimum (lower n) (N n) (H n - i) (horder n)
          (RootIndexed.subtreeStepFieldVector (roots n field) (installed n field))} ≤
        ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  intro lower τ hτ trials installed roots P
  obtain ⟨p, hp, hwindow⟩ :=
    eventually_countableRootEndpointMinimum_ge_le_polynomial_sub_horizon hN μ hnorm
      hcross hsigma hcentered ha ha1 ht hgap hH hT horder
  refine ⟨p, hp, ?_⟩
  filter_upwards [hwindow, htrials] with n hn htrial
  let _ := horder n
  classical
  refine measure_stoppedResetEndpoint_ge_le (Root := Root) (α := ℕ) (lower n) hnodePath
    μ hnorm (N n) initialPosition R (growth n) hR (hgrowth n) (upper n) (duration n)
    htrial.1 htrial.2.1 htrial.2.2 r (H n) (T n) _ _ ?_
  intro i hi
  let x := ζ * Real.log (N n : ℝ)
  have hmap := congrArg (fun law : Measure ℝ => law (Set.Ici x))
    (countableRootEndpointMinimum_map_eq μ (lower n) (N n) (H n - i))
  rw [Measure.map_apply (measurable_countableRootEndpointMinimum (lower n) (N n) (H n - i))
      measurableSet_Ici,
    Measure.map_apply (measurable_firstNSelectedEndpointMinimum (lower n) (N n) (H n - i))
      measurableSet_Ici] at hmap
  exact hmap.ge.trans (hn i hi)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
