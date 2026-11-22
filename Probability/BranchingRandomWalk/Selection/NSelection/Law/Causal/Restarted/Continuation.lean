/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Stopping
public import Probability.BranchingRandomWalk.Population.Processes.Selected.Continuation
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Continuation of the stopped rank-installed process

## Public declarations

* `RootIndexed.stoppedRankInstalledTrajectoryField_continuation_on_cell`:
  on the cell $A=E\cap\{\tau=n, P_n=S\}$ with $E\in\mathcal F_n$,
  enumerate $S$ by $u_i$. The joint law of their positions $X$ and descendant
  fields $V$ is $\mathcal L_A(X,V)=\mathcal L_A(X)\otimes Q_{|S|}$.
  At all later generations $n+k$, the actual population is the image of
  the first-$N$ population at time $k$ driven by $(X,V)$, with the inherited
  order on descendant labels.
-/

open MeasureTheory ProbabilityTheory

public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Coupling

variable {Root α : Type*} [MeasurableSpace (RootIndexed.TreeNode Root α)]
  [Countable (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode Root α)]

local notation "Ωf" => RootIndexed.StepField (Root ⊕ Root) α ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)

/-- The joint stopped-past and future law on a selected-population cell,
together with the pathwise identification of the selected continuation. -/
theorem RootIndexed.stoppedRankInstalledTrajectoryField_continuation_on_cell
    {κ : Type*} [Fintype κ] [LinearOrder (RootIndexed.TreeNode κ α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (initialRoots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (n : ℕ) (roots : κ → RootIndexed.TreeNode Root α)
    (hdepth : ∀ i, (roots i).2.length = n) (hinj : Function.Injective roots)
    (horder : ∀ p q : RootIndexed.TreeNode κ α, p < q ↔
      ((roots p.1).1, (roots p.1).2 ++ p.2) < ((roots q.1).1, (roots q.1).2 ++ q.2))
    (E : Set Ωf) (hE : MeasurableSet[𝔽 n] E) :
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N initialRoots
      initialPosition hP τ hτ
    let stage := RootIndexed.restartedRealPositionNSelectedBRWField N initialRoots
      initialPosition id hP.toFinset n
    let A := E ∩ {ω | τ ω = n ∧ RootIndexed.selectedPopulationTotalized N initialRoots
      initialPosition id id n (stage ω) = Finset.univ.image roots}
    let X := fun ω => RootIndexed.subtreeInitialPosition initialPosition id (stage ω) roots
    let V := fun ω => RootIndexed.subtreeStepFieldVector roots (installed ω)
    let law := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    MeasurableSet[𝔽 n] A ∧
    Measurable[𝔽 n] X ∧
    AEMeasurable (fun ω => (X ω, V ω)) (law.restrict A) ∧
    (law.restrict A).map (fun ω => (X ω, V ω)) =
      ((law.restrict A).map X).prod (RootIndexed.stepFieldLaw μ) ∧
    ∀ ω ∈ A, ∀ k, RootIndexed.selectedPopulationTotalized N initialRoots initialPosition
      id id (n + k) (installed ω) =
        (RootIndexed.selectedPopulationTotalized N Finset.univ (X ω) id id k (V ω)).image
          (fun p => ((roots p.1).1, (roots p.1).2 ++ p.2)) := by
  intro installed stage A X V law
  have hstage :
      @Measurable Ωf (RootIndexed.StepField Root α ℝ) (𝔽 n)
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ) n) stage :=
    RootIndexed.restartedRealPositionNSelectedBRWField_filtration_measurable
      N initialRoots initialPosition hP n
  have hpop : Measurable[𝔽 n] (fun ω => RootIndexed.selectedPopulationTotalized N initialRoots
      initialPosition id id n (stage ω)) :=
    (RootIndexed.selectedPopulationTotalized_adapted N initialRoots initialPosition
      id measurable_id id measurable_id n).comp hstage
  have hcell : MeasurableSet[𝔽 n] A := by
    have htime : MeasurableSet[𝔽 n] {ω | τ ω = n} := hτ.measurableSet_eq n
    exact hE.inter (htime.inter (hpop (measurableSet_singleton _)))
  have hX : Measurable[𝔽 n] X := by
    let _ : MeasurableSpace Ωf := 𝔽 n
    apply measurable_pi_iff.mpr
    intro i
    have hm := (RootIndexed.positionAtGeneration_measurable initialPosition id
      measurable_id n (roots i).1 (roots i).2).comp hstage
    have heq : (fun ω => RootIndexed.positionAtGeneration initialPosition id n
        (roots i).1 (roots i).2 (stage ω)) = fun ω => X ω i := by
      funext ω
      simp [X, RootIndexed.subtreeInitialPosition, RootIndexed.positionAtGeneration, hdepth i]
    change Measurable (fun ω => RootIndexed.positionAtGeneration initialPosition id n
      (roots i).1 (roots i).2 (stage ω)) at hm
    rw [heq] at hm
    exact hm
  have hXfull : Measurable X := hX.mono ((𝔽).le n) le_rfl
  let rightRoots (i : κ) : RootIndexed.TreeNode (Root ⊕ Root) α :=
    (Sum.inr (roots i).1, (roots i).2)
  let W : Ωf → RootIndexed.StepField κ α ℝ := RootIndexed.subtreeStepFieldVector rightRoots
  have hW : Measurable W := RootIndexed.subtreeStepFieldVector_measurable rightRoots
  have hVW : V =ᵐ[law.restrict A] W := by
    apply (ae_restrict_iff' (((𝔽).le n) _ hcell)).mpr
    exact Filter.Eventually.of_forall fun ω hω => by
      funext i v
      exact RootIndexed.stoppedRankInstalledTrajectoryField_apply_of_le_length
        N initialRoots initialPosition hP τ hτ ω n hω.2.1 _ _ (by
          rw [List.length_append, hdepth i]
          exact Nat.le_add_right _ _)
  have hpair : Measurable (fun ω => (X ω, W ω)) := hXfull.prodMk hW
  have hagree : (fun ω => (X ω, V ω)) =ᵐ[law.restrict A] fun ω => (X ω, W ω) :=
    hVW.mono fun ω h => congrArg (Prod.mk (X ω)) h
  refine ⟨hcell, hX, hpair.aemeasurable.congr hagree.symm,
    (Measure.map_congr hagree).trans ?_, ?_⟩
  · apply Measure.ext_prod
    intro S T hS hT
    rw [Measure.map_apply hpair (hS.prod hT), Measure.prod_prod,
      Measure.map_apply hXfull hS, Measure.restrict_apply (hXfull hS),
      Measure.restrict_apply (hpair (hS.prod hT))]
    have hright : Function.Injective rightRoots := by
      intro i j heq
      exact hinj (Prod.ext (Sum.inr_injective (congrArg Prod.fst heq))
        (congrArg (fun p : RootIndexed.TreeNode (Root ⊕ Root) α => p.2) heq))
    have hfactor := RootIndexed.subtreeStepFieldVector_event_factorization μ rightRoots hdepth hright
      (X ⁻¹' S ∩ A) T ((hX hS).inter hcell) hT
    simpa only [law, W, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      show (fun ω => (X ω, W ω)) ⁻¹' (S ×ˢ T) = X ⁻¹' S ∩ W ⁻¹' T from rfl] using hfactor
  · intro ω hω k
    have heq : installed ω = stage ω :=
      RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage
        N initialRoots initialPosition hP τ hτ ω n hω.2.1
    dsimp only [X, V]
    rw [heq]
    exact RootIndexed.selectedPopulationTotalized_eq_image_subtrees N initialRoots
      initialPosition id id (stage ω) n roots hdepth hinj hω.2.2.symm horder k

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
