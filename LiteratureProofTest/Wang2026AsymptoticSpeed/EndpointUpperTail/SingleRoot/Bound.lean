/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.HorizonWindow
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.EntranceProbability
import all LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.SingleRoot.ResetEndpoint
public import Combinatorics.UlamHarris.Order
public import Probability.BranchingRandomWalk.Step.Ordering.Law
public import Probability.BranchingRandomWalk.Assumptions.Moments
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.EndpointOrder

/-!
# Endpoint upper tail from a single initial particle

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_singleRootEndpointMinimum_ge_le_polynomial`: if $N_i\to\infty$,
  $H_i/\log^3 N_i\to t>0$ and $\zeta>\frac{\pi^2}2\sigma^2t$, the minimum of
  the $N_i$-selection process started from a single particle at zero
  satisfies $\mathbb P(M_{H_i}\ge\zeta\log N_i)\le N_i^{-b}$ eventually
  for some $b>0$. The offspring law has boundary normalization,
  finite tilted variance and cross-weight, nonempty supercritical offspring,
  and a positive exponential moment of the leftmost displacement.

This is the $a=0$ upper bound of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

public section

namespace LiteratureProofTest.Wang2026AsymptoticSpeed

open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath

open ProbabilityTheory

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
open SelectedPath.Completion.Lemmas

noncomputable local instance singleRootAddressOrder : LinearOrder (RootIndexed.TreeNode ℕ ℕ) :=
  RootIndexed.addressLinearOrder ℕ ℕ

noncomputable local instance (priority := high) singleRootAddressDecidableEq {R : Type*}
    [LinearOrder (RootIndexed.TreeNode R ℕ)] : DecidableEq (RootIndexed.TreeNode R ℕ) :=
  LinearOrder.toDecidableEq

/-- The polynomial endpoint upper tail, with a single initial root, obtained
by the stopped entrance and remaining-horizon estimates. -/
theorem eventually_singleRootEndpointMinimum_ge_le_polynomial
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnorm : HasBoundaryNormalization L.potential L.raw)
    (hcross : HasFiniteCrossWeight L.potential L.raw)
    (hsuper : BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hne : L.raw nonemptySupport = 1)
    (hexp : HasLeftmostPositiveExponentialMoment L)
    {σ : ℝ} (hσ : 0 < σ)
    (hcentered : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (σ ^ 2))
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t ζ : ℝ} (ht : 0 < t)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hζ : (Real.pi ^ 2 / 2) * σ ^ 2 * t < ζ) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ n in atTop,
      P {field | ζ * Real.log (N n : ℝ) ≤
        @countableRootEndpointMinimum 1 (N n) (H n) (RootIndexed.addressLinearOrder (Fin 1) ℕ)
          field} ≤ ENNReal.ofReal (Real.exp (-b * Real.log (N n : ℝ))) := by
  intro P
  let μ := L.sortedPotentialImage
  let Q := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
  let critical := (Real.pi ^ 2 / 2) * σ ^ 2 * t
  let η := (ζ - critical) / 2
  have hη : 0 < η := by dsimp [η, critical]; linarith
  let ζ' := ζ - η
  have hζ' : critical < ζ' := by dsimp [ζ', η, critical]; linarith
  have hμnorm := L.sortedPotentialImage_hasBoundaryNormalization hnorm
  have hμcross := L.sortedPotentialImage_hasFiniteCrossWeight hnorm hcross
  have hμne : μ nonemptySupport = 1 := by
    rw [show μ = L.sortedPotentialImage from rfl, L.sortedPotentialImage_nonemptySupport,
      L.sorted_nonemptySupport, hne]
  obtain ⟨a, ha, ha1, R, growth, hR, hgrowth, upper, duration, γ, _, hT, hTH, b, hb, hbad⟩ :=
    exists_logarithmicEntrance_failure_le_polynomial L hsuper hne hexp hμnorm hN ht hH hη
  have hζgap : -a + (Real.pi ^ 2 / 2) * σ ^ 2 * t < ζ' := by
    change -a + critical < ζ'
    linarith
  obtain ⟨p, hp, htail⟩ :=
    LiteratureProofTest.Wang2026AsymptoticSpeed.SingleRoot.eventually_measure_actualEndpoint_ge_le_badEntrance_add_polynomial μ hμnorm hμcross hμne
      hN hσ hcentered ha ha1 ht hζgap hH hT hTH (fun _ => RootIndexed.addressLinearOrder _ ℕ)
      (0 : ℕ) R growth hR hgrowth upper duration (fun n => η * Real.log (N n : ℝ))
  let β := min b p / 2
  have hβ : 0 < β := by dsimp [β]; exact div_pos (lt_min hb hp) two_pos
  have hlog : Tendsto (fun n => Real.log (N n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have habsorb : ∀ᶠ n in atTop, 2 ≤ Real.exp (β * Real.log (N n : ℝ)) :=
    (Real.tendsto_exp_atTop.comp (hlog.const_mul_atTop hβ)).eventually_ge_atTop 2
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hbad, htail, habsorb, hlog.eventually_ge_atTop 0,
    hN.eventually_ge_atTop 1] with n hn ht' habsorb hlogn hNn
  let logN := Real.log (N n : ℝ)
  let x := ζ * logN
  let lower := ⌈(N n : ℝ) ^ a⌉₊
  let τ := SelectedPath.Completion.time R growth hR hgrowth lower (upper n) (duration n) (0 : ℕ)
  let hτ := SelectedPath.Completion.time_isStoppingTime R growth hR hgrowth
    lower (upper n) (duration n) (0 : ℕ)
  let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
    (upper n) (duration n) (0 : ℕ)
  let installed := RootIndexed.stoppedRankInstalledTrajectoryField (N n) ({0} : Finset ℕ)
    (fun _ => 0) trials τ hτ
  let B := RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) (N n) ({0} : Finset ℕ)
    (fun _ => 0) (H n) x
  have hx : ζ' * logN + η * logN = x := by dsimp [ζ', x]; ring
  rw [hx] at ht'
  have hb' : 2 * β ≤ b := by dsimp [β]; linarith [min_le_left b p]
  have hp' : 2 * β ≤ p := by dsimp [β]; linarith [min_le_right b p]
  let w := Real.exp (-(2 * β) * logN)
  have hnB : Q (installed ⁻¹' B) ≤ ENNReal.ofReal (Real.exp (-β * logN)) := by
    have hg₁ : Real.exp (-b * logN) ≤ w :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hb' hlogn])
    have hg₂ : Real.exp (-p * logN) ≤ w :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hp' hlogn])
    have htotal := ht'.trans (add_le_add (hn.trans (ENNReal.ofReal_le_ofReal hg₁))
      (ENNReal.ofReal_le_ofReal hg₂))
    change Q (installed ⁻¹' B) ≤ _ at htotal
    refine htotal.trans ?_
    have hw : 0 ≤ w := Real.exp_nonneg _
    rw [← ENNReal.ofReal_add hw hw]
    apply ENNReal.ofReal_le_ofReal
    calc
      w + w = w * 2 := by ring
      _ ≤ w * Real.exp (β * logN) := mul_le_mul_of_nonneg_left habsorb hw
      _ = _ := by dsimp [w]; rw [← Real.exp_add]; congr 1; ring
  obtain ⟨hm, hlaw⟩ := RootIndexed.stoppedRankInstalledTrajectoryField_measurable_law
    μ (N n) ({0} : Finset ℕ) (fun _ => 0) trials τ hτ
  have hB : MeasurableSet B := RootIndexed.measurableSet_selectedPopulationEndpointAtLeast
    (N n) ({0} : Finset ℕ) (fun _ => 0) (H n) x
  have hactual : P B = Q (installed ⁻¹' B) := by
    change Q.map installed = P at hlaw
    calc
      P B = (Q.map installed) B := congrArg (fun m : Measure _ => m B) hlaw.symm
      _ = _ := Measure.map_apply hm hB
  let oneOrder : LinearOrder (RootIndexed.TreeNode (Fin 1) ℕ) := RootIndexed.addressLinearOrder (Fin 1) ℕ
  let _ : LinearOrder (RootIndexed.TreeNode (Fin 1) ℕ) := oneOrder
  have horder (u v : RootIndexed.TreeNode (Fin 1) ℕ) :
      @LT.lt _ oneOrder.toLT u v ↔
        @LT.lt _ singleRootAddressOrder.toLT (u.1.val, u.2) (v.1.val, v.2) := by
    rw [RootIndexed.addressLinearOrder_lt_iff (Fin 1) ℕ, RootIndexed.addressLinearOrder_lt_iff ℕ ℕ]
    simp [Fin.ext_iff]
  let B₁ := RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) (N n) Finset.univ
    (fun _ : Fin 1 => (0 : ℝ)) (H n) x
  have hrelabel : P B = finiteRootStepFieldLaw μ 1 B₁ := by
    have hroots : Finset.univ.image (Fin.val : Fin 1 → ℕ) = {0} := by
      ext j
      simp [Fin.val_eq_zero]
    have h := RootIndexed.measure_selectedPopulationEndpointAtLeast_relabel
      μ (Fin.val : Fin 1 → ℕ) Fin.val_injective horder (N n) (fun _ => 0) (H n) x
    rw [hroots] at h
    exact h
  have hsame : B₁ =ᵐ[finiteRootStepFieldLaw μ 1]
      {field | x ≤ firstNSelectedEndpointMinimum 1 (N n) (H n) field} := by
    filter_upwards [firstNSelectedEndpointMinimum_eq_population_inf'_ae
      1 (N n) (H n) (by decide) hNn μ hμnorm hμne] with field hfield
    obtain ⟨hpop, hmin⟩ := hfield
    rw [hmin, Finset.le_inf'_iff]
    have heq : firstNSelectedPopulation 1 (N n) (H n) field =
        RootIndexed.selectedPopulationTotalized (N n) Finset.univ
          (fun _ : Fin 1 => (0 : ℝ)) id id (H n) field := by
      unfold firstNSelectedPopulation
      congr 1
      exact Subsingleton.elim _ _
    rw [heq]
    rfl
  have hmap := congrArg (fun M : Measure ℝ => M (Set.Ici x))
    (countableRootEndpointMinimum_map_eq μ 1 (N n) (H n))
  rw [Measure.map_apply (measurable_countableRootEndpointMinimum 1 (N n) (H n)) measurableSet_Ici,
    Measure.map_apply (measurable_firstNSelectedEndpointMinimum 1 (N n) (H n)) measurableSet_Ici] at hmap
  exact hmap.le.trans ((measure_congr hsame).ge.trans (hrelabel.ge.trans (hactual.le.trans hnB)))

end LiteratureProofTest.Wang2026AsymptoticSpeed

end
