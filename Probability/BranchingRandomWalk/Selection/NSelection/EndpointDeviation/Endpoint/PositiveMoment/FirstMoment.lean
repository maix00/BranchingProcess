/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Basic
public import Probability.BranchingRandomWalk.Assumptions.Moments
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Closure
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.PredictableAddress
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Lemmas.Lineage

/-!
# First moments of the selected endpoint

## Public declarations

* `finiteRootStepFieldLaw_integrable_exp_neg_firstNSelectedEndpointMinimum`:
  with boundary normalization and almost surely nonempty offspring,
  $e^{-M_H}$ is integrable for a process with positive capacity and $m>0$
  zero-position roots.
* `finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum`:
  under the additional leftmost first moment, $M_H$ is integrable.
  At each generation the leftmost selected parent's leftmost child gives
  $M_{k+1}\le M_k+|D_k|$, where $D_k$ has the law of the leftmost displacement.

This proves the endpoint first-moment estimates in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Appendix A, Lemmas A.2, A.3, and A.5. The one-particle
comparison is realized by reading fresh offspring marks at predictable
leftmost addresses in the actual finite-root field.
-/

open Filter MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris

/-- The exponential endpoint moment in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Appendix A, Lemma A.2, gives integrability of $e^{-M_H}$. -/
theorem finiteRootStepFieldLaw_integrable_exp_neg_firstNSelectedEndpointMinimum
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    Integrable (fun field => Real.exp (-firstNSelectedEndpointMinimum m N H field))
      (finiteRootStepFieldLaw μ m) := by
  have hM := measurable_firstNSelectedEndpointMinimum m N H
  refine ⟨(Real.continuous_exp.measurable.comp hM.neg).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => Real.exp_nonneg _)]
  exact (finiteRootStepFieldLaw_lintegral_exp_neg_firstNSelectedEndpointMinimum_le
    m N H hm hN μ hboundary hnonempty).trans_lt ENNReal.ofReal_lt_top

/-- The endpoint has a finite first moment under the leftmost first-moment
assumption. This combines Lemmas A.3 and A.5 of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Appendix A. -/
theorem finiteRootStepFieldLaw_integrable_firstNSelectedEndpointMinimum
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (m N H : ℕ) (hm : 0 < m) (hN : 0 < N)
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1)
    (hfirst : HasLeftmostFirstMoment L) :
    Integrable (firstNSelectedEndpointMinimum m N H)
      (finiteRootStepFieldLaw L.sortedPotentialImage m) := by
  let μ := L.sortedPotentialImage
  let P := finiteRootStepFieldLaw μ m
  let M := firstNSelectedEndpointMinimum m N
  let chosen (k : ℕ) := firstNSelectedEndpointMinAddressAtDepth m N k hm
  let mark (k : ℕ) (field : FiniteRootStepField m ℕ ℝ) :=
    field (chosen k field).1 (chosen k field).2
  let D (k : ℕ) (field : FiniteRootStepField m ℕ ℝ) := |value' (mark k field) 0|
  have hD (k : ℕ) : Integrable (D k) P := by
    let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
    have hchosen : Measurable[F k] (chosen k) :=
      measurable_firstNSelectedEndpointMinAddressAtDepth m N k hm
    have hfiber (p : RootIndexed.TreeNode (Fin m) ℕ) :
        MeasurableSet[F k] {field | chosen k field = p} :=
      hchosen (measurableSet_singleton p)
    have hdepth := firstNSelectedEndpointMinAddressAtDepth_length m N k hm
    have hmarkMap : P.map (mark k) = μ :=
      RootIndexed.stepFieldLaw_predictableAddress_map_eq μ (chosen k) hfiber hdepth
        (Set.to_countable _)
    have hmark : Measurable (mark k) := by
      have hmeas :
          Measurable (fun (p : FiniteRootStepField m ℕ ℝ ×
            RootIndexed.TreeNode (Fin m) ℕ) => p.1 p.2.1 p.2.2) :=
        measurable_from_prod_countable_left fun p =>
          (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
      exact hmeas.comp (measurable_id.prodMk (hchosen.mono (F.le k) le_rfl))
    have hslot := L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
    exact ((hmarkMap.symm ▸ hslot : Integrable
      (fun ξ : Step ℕ ℝ => |value' ξ 0|) (P.map (mark k))).comp_aemeasurable
      hmark.aemeasurable)
  have hupper : ∀ᵐ field ∂P, ∀ n, M n field ≤ ∑ k ∈ Finset.range n, D k field := by
    filter_upwards [finiteRootStepFieldLaw_endpointMinimum_succ_le_predictablePositiveSlotZero_ae
      m N hm hN L hboundary hnonempty] with field hs n
    induction n with
    | zero => simp [M, firstNSelectedEndpointMinimum_zero_eq m N hm]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (hs n).trans (add_le_add ih (max_le (le_abs_self _) (abs_nonneg _)))
  have hboundaryμ := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have hExp := finiteRootStepFieldLaw_integrable_exp_neg_firstNSelectedEndpointMinimum
    m N H hm hN μ hboundaryμ hnonemptyμ
  have hsum : Integrable (fun field => ∑ k ∈ Finset.range H, D k field) P :=
    integrable_finsetSum _ fun k _ => hD k
  apply (hsum.add hExp).mono' (measurable_firstNSelectedEndpointMinimum m N H).aestronglyMeasurable
  filter_upwards [hupper] with field hs
  simp only [Real.norm_eq_abs, Pi.add_apply]
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range H, D k field :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hneg := Real.add_one_le_exp (-M H field)
  rw [abs_le]
  constructor <;> linarith [Real.exp_nonneg (-M H field), hs H]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
