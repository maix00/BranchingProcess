/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Selected.ParameterizedRootIndexed
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.EndpointOrder
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import MeasureTheory.Integral.UpperTailOrder

/-!
# Expectation comparison for selected endpoints

## Public declarations

* `RootIndexed.integral_selectedPopulationEndpointWithParameter_le_add_of_embedding`:
  if the initial cloud `x` has $m$ distinct particles with positions at most
  $c$, then its mean endpoint is at most $c+\mathbb E[M_H^{m}]$, where
  $M_H^{m}$ starts from $m$ particles at zero and has the same capacity.

The comparison applies the initial-population order of WANG Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Corollary 3.10 and Corollary 3.11, to integrable
endpoints.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching Combinatorics.UlamHarris

local instance (priority := high) meanAddressDecidableEq
    {s : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)] :
    DecidableEq (RootIndexed.TreeNode (Fin s) ℕ) :=
  LinearOrder.toDecidableEq

private theorem measure_endpoint_ge_eq
    {s : ℕ} [MeasurableSpace (RootIndexed.TreeNode (Fin s) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin s) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    (N H : ℕ) (hN : 0 < N) (hs : 0 < s) (x : Fin s → ℝ) (z : ℝ) :
    let P := RootIndexed.stepFieldLaw (Root := Fin s) μ
    P {field | z ≤ RootIndexed.selectedPopulationEndpointWithParameter s N H (x, field)} =
      P (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ x H z) := by
  intro P
  apply measure_congr
  filter_upwards [RootIndexed.selectedPopulationTotalized_nonempty_ae N
    (Finset.univ : Finset (Fin s)) ⟨⟨0, hs⟩, Finset.mem_univ _⟩ x hN μ hboundary hne]
    with field hfield
  have hnonempty : (RootIndexed.selectedPopulationWithParameter s N H (x, field)).Nonempty :=
    hfield H
  rw [Set.mem_ofPred_eq, RootIndexed.selectedPopulationEndpointWithParameter, dite_eq_left hnonempty,
    Finset.le_inf'_iff]
  simp only [RootIndexed.selectedPopulationWithParameter, RootIndexed.selectedPopulationEndpointAtLeast]
  change (∀ p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ x id id H field,
    z ≤ RootIndexed.observedPositionAtGeneration x id id H field p) ↔
    ∀ p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ x id id H field,
      z ≤ RootIndexed.position x id field p.1 p.2
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  rw [RootIndexed.observedPositionAtGeneration_eq x id id H field p
    (RootIndexed.selectedPopulationTotalized_depth N Finset.univ x id id H field p hp)]
  rfl

/-- Initial-cloud order and spatial translation imply the corresponding
inequality for integrable endpoint expectations. -/
public theorem RootIndexed.integral_selectedPopulationEndpointWithParameter_le_add_of_embedding
    {m s : ℕ} [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin s) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin s) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    (N H : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N)
    (x : Fin s → ℝ) (e : Fin m ↪ Fin s) (c : ℝ) (hx : ∀ i, x (e i) ≤ c)
    (hxint : Integrable (fun field => RootIndexed.selectedPopulationEndpointWithParameter
      s N H (x, field)) (RootIndexed.stepFieldLaw μ))
    (hzero : Integrable (fun field => RootIndexed.selectedPopulationEndpointWithParameter
      m N H ((fun _ => 0), field)) (RootIndexed.stepFieldLaw μ)) :
    (∫ field, RootIndexed.selectedPopulationEndpointWithParameter s N H (x, field)
      ∂RootIndexed.stepFieldLaw μ) ≤ c +
      ∫ field, RootIndexed.selectedPopulationEndpointWithParameter m N H ((fun _ => 0), field)
        ∂RootIndexed.stepFieldLaw μ := by
  let P := RootIndexed.stepFieldLaw (Root := Fin s) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin m) μ
  let F := fun field => RootIndexed.selectedPopulationEndpointWithParameter s N H (x, field)
  let G := fun field => RootIndexed.selectedPopulationEndpointWithParameter m N H ((fun _ => 0), field)
  have hs : 0 < s := Fin.pos_iff_nonempty.mpr ⟨e ⟨0, hm⟩⟩
  have hF : Measurable F :=
    (RootIndexed.measurable_selectedPopulationEndpointWithParameter s N H).comp
      (measurable_const.prodMk measurable_id)
  have hG : Measurable G :=
    (RootIndexed.measurable_selectedPopulationEndpointWithParameter m N H).comp
      (measurable_const.prodMk measurable_id)
  have htail (z : ℝ) : P {field | z ≤ F field} ≤ Q {field | z ≤ c + G field} := by
    change P {field | z ≤ RootIndexed.selectedPopulationEndpointWithParameter s N H (x, field)} ≤ _
    rw [measure_endpoint_ge_eq μ hboundary hne N H hN hs x z]
    have hc := RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_cloudEmbedding μ
      hboundary N hN (by simpa using hmN) (fun _ => (0 : ℝ) + c) x e (by simpa using hx)
      H ((z - c) + c)
    rw [RootIndexed.selectedPopulationEndpointAtLeast_add_initial] at hc
    simp only [sub_add_cancel] at hc
    refine hc.trans_eq ?_
    rw [← measure_endpoint_ge_eq μ hboundary hne N H hN hm (fun _ => 0) (z - c)]
    congr 1
    ext field
    simp only [Set.mem_ofPred_eq, G]
    exact sub_le_iff_le_add'
  have hFi : Integrable F P := by convert hxint using 3
  have hGi : Integrable G Q := by convert hzero using 3
  have h := integral_le_of_measure_ge_le (P := P) (Q := Q) (f := F)
    (g := fun field => c + G field) hFi ((integrable_const c).add hGi)
    hF (measurable_const.add hG) htail
  rw [integral_add (integrable_const c) hGi, integral_const, probReal_univ, one_smul] at h
  convert h using 5

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
