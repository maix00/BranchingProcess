/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Selected.ParameterizedRootIndexed
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position
import Probability.BranchingRandomWalk.Population.Processes.Selected.Continuation

/-!
# Endpoint law on a fixed generation's population cell

## Public declarations

* `RootIndexed.selectedEndpoint_continuation_on_cell`: condition on a
  generation-$n$ event where the actual selected population has fixed
  addresses $u_i$. If $X$ is their position vector and $V$ their descendant
  field, the joint restricted law is $\mathcal L_A(X,V)=\mathcal L_A(X)\otimes Q$.
  The endpoint at $n+k$ is the endpoint at $k$ for initial vector $X$ and
  field $V$, using the order induced by concatenation of the addresses.
* `RootIndexed.selectedPopulationEndpointWithParameter_zero_eq_inf` gives
  $M_0=\min_i X_i$ for a nonempty initial vector.

Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Lemma 2.1 and Theorem 1.2.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching Combinatorics.UlamHarris

/-- At generation zero the endpoint is the minimum of the initial vector. -/
public theorem RootIndexed.selectedPopulationEndpointWithParameter_zero_eq_inf
    {s : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)]
    (N : ℕ) (x : Fin s → ℝ) (field : RootIndexed.StepField (Fin s) ℕ ℝ)
    (hne : (Finset.univ : Finset (Fin s)).Nonempty) :
    RootIndexed.selectedPopulationEndpointWithParameter s N 0 (x, field) =
      Finset.univ.inf' hne x := by
  unfold RootIndexed.selectedPopulationEndpointWithParameter RootIndexed.selectedPopulationWithParameter
  simp only [RootIndexed.selectedPopulationTotalized,
    RootIndexed.initialPopulation, Finset.map_eq_image]
  change (if h : (Finset.univ.image (fun i : Fin s => (i, ([] : List ℕ)))).Nonempty then
    (Finset.univ.image (fun i : Fin s => (i, ([] : List ℕ)))).inf' h
      (RootIndexed.observedPositionAtGeneration x id id 0 field) else 0) = _
  rw [dite_eq_left (hne.image _), Finset.inf'_image]
  apply Finset.inf'_congr hne rfl
  intro i _
  simp [Function.comp_apply, RootIndexed.observedPositionAtGeneration,
    RootIndexed.positionAtGeneration, RootIndexed.position, RootIndexed.displace,
    Combinatorics.Branching.displaceWith]

/-- The finite-horizon endpoint after branching from the selected population
on a deterministic generation cell. -/
public theorem RootIndexed.selectedEndpoint_continuation_on_cell
    {m s : ℕ} [mOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    [sOrder : LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (initial : Fin m → ℝ) (n : ℕ)
    (roots : Fin s ↪ RootIndexed.TreeNode (Fin m) ℕ)
    (hdepth : ∀ i, (roots i).2.length = n)
    (horder : ∀ p q : RootIndexed.TreeNode (Fin s) ℕ, @LT.lt _ sOrder.toLT p q ↔
      @LT.lt _ mOrder.toLT ((roots p.1).1, (roots p.1).2 ++ p.2)
        ((roots q.1).1, (roots q.1).2 ++ q.2)) :
    let A := {ω | RootIndexed.selectedPopulationWithParameter m N n (initial, ω) =
      Finset.univ.image roots}
    let X := fun ω => RootIndexed.subtreeInitialPosition initial id ω roots
    let V := RootIndexed.subtreeStepFieldVector roots
    let P := RootIndexed.stepFieldLaw (Root := Fin m) μ
    MeasurableSet A ∧ Measurable X ∧ Measurable V ∧
    (P.restrict A).map (fun ω => (X ω, V ω)) =
      ((P.restrict A).map X).prod (RootIndexed.stepFieldLaw μ) ∧
    ∀ ω ∈ A, ∀ k,
      RootIndexed.selectedPopulationEndpointWithParameter m N (n + k) (initial, ω) =
        RootIndexed.selectedPopulationEndpointWithParameter s N k (X ω, V ω) := by
  intro A X V P
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  have hpop : Measurable[F n] (fun ω =>
      RootIndexed.selectedPopulationWithParameter m N n (initial, ω)) :=
    RootIndexed.selectedPopulationTotalized_adapted N Finset.univ initial
      id measurable_id id measurable_id n
  have hA : MeasurableSet[F n] A := by
    have hh := hpop (measurableSet_singleton (Finset.univ.image roots))
    convert hh using 2
    ext ω
    simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  have hX : Measurable[F n] X := by
    let _ : MeasurableSpace (RootIndexed.StepField (Fin m) ℕ ℝ) := F n
    apply measurable_pi_iff.mpr
    intro i
    have hb := RootIndexed.positionAtGeneration_measurable initial id
      measurable_id n (roots i).1 (roots i).2
    have heq : (fun ω => RootIndexed.positionAtGeneration initial id n
        (roots i).1 (roots i).2 ω) = fun ω => X ω i := by
      funext ω
      simp [X, RootIndexed.subtreeInitialPosition, RootIndexed.positionAtGeneration, hdepth i]
    rw [← heq]
    exact hb
  have hXfull : Measurable X := hX.mono (F.le n) le_rfl
  have hV : Measurable V := RootIndexed.subtreeStepFieldVector_measurable roots
  have hAfull : MeasurableSet A := F.le n _ hA
  refine ⟨hAfull, hXfull, hV, ?_, ?_⟩
  · apply Measure.ext_prod
    intro S T hS hT
    rw [Measure.map_apply (hXfull.prodMk hV) (hS.prod hT), Measure.prod_prod,
      Measure.map_apply hXfull hS, Measure.restrict_apply (hXfull hS),
      Measure.restrict_apply ((hXfull.prodMk hV) (hS.prod hT))]
    have hfactor := RootIndexed.subtreeStepFieldVector_event_factorization μ roots hdepth
      roots.injective (X ⁻¹' S ∩ A) T ((hX hS).inter hA) hT
    simpa only [P, V, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      show (fun ω => (X ω, V ω)) ⁻¹' (S ×ˢ T) = X ⁻¹' S ∩ V ⁻¹' T from rfl] using hfactor
  · intro ω hω k
    let embed (p : RootIndexed.TreeNode (Fin s) ℕ) : RootIndexed.TreeNode (Fin m) ℕ :=
      ((roots p.1).1, (roots p.1).2 ++ p.2)
    let Pop := RootIndexed.selectedPopulationWithParameter s N k (X ω, V ω)
    have ha : RootIndexed.selectedPopulationWithParameter m N n (initial, ω) =
        Finset.univ.image roots := by
      convert hω using 1
    have hp : RootIndexed.selectedPopulationWithParameter m N (n + k) (initial, ω) =
        Pop.image embed := by
      have hh := RootIndexed.selectedPopulationTotalized_eq_image_subtrees N Finset.univ initial id id ω
        n roots hdepth roots.injective (by
          unfold RootIndexed.selectedPopulationWithParameter at ha
          convert ha.symm using 2) horder k
      unfold Pop RootIndexed.selectedPopulationWithParameter
      convert hh using 2
      congr 1
      exact Subsingleton.elim _ _
    unfold RootIndexed.selectedPopulationEndpointWithParameter
    rw [hp]
    dsimp only
    by_cases hne : Pop.Nonempty
    · rw [dite_eq_left (hne.image _), dite_eq_left hne]
      rw [Finset.inf'_image]
      apply Finset.inf'_congr hne rfl
      intro p hmem
      have hd : p.2.length = k :=
        RootIndexed.selectedPopulationTotalized_depth N Finset.univ
          (X ω) id id k (V ω) p hmem
      have he : (embed p).2.length = n + k := by
        simp [embed, List.length_append, hdepth p.1, hd]
      dsimp only [Function.comp_apply]
      rw [RootIndexed.observedPositionAtGeneration_eq initial id id (n + k) ω (embed p) he,
        RootIndexed.observedPositionAtGeneration_eq (X ω) id id k (V ω) p hd]
      exact (RootIndexed.position_subtreeStepFieldVector initial id ω roots p.1 p.2).symm
    · have hempty : ¬ (Pop.image embed).Nonempty := by simpa using hne
      rw [dite_eq_right hempty, dite_eq_right hne]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
