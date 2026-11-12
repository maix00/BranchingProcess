/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Endpoint
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.RootFamily
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.Geometry
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.FreshField
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Endpoint positions and fresh-field independence

## Public declarations

* selectedReserveSpineRestartEndpointPositionFreshField_jointLaw_on_finite states that, on the
  finite first-success endpoint event, the joint law of the endpoint-position vector and its
  descendant field rooted at the selected endpoint particles is the product of the restricted
  endpoint-position law and the independent finite-root product field law.

With \(P\) the two-root step-field law, \(Q\) the \(\mathrm{Fin}(\mathrm{lower})\)-root
step-field law, \(E=\{f:\tau(f)<\infty\}\), and \(V(f)=\mathrm{positions}(f)\), set
\[
  F(f)(i,w)=f\bigl(\mathrm{inr}(r),
    (\mathrm{endpointRankVector}(f)(i)).2\mathbin{+\!\!+}w\bigr).
\]
Here endpointRankVector is the rank-installed endpoint vector defined in Endpoint.lean.
The theorem states
\[
  (P|_{\{\tau<\infty\}})\circ(V,F)^{-1}
  =((P|_{\{\tau<\infty\}})\circ V^{-1})\otimes Q.
\]

The stopped-time root measurability argument is local to this law. The two conditional
factorization steps and the reserve-spine BRW fallback root construction are in
Completion/Lemmas/EndpointHorizon/.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

namespace ProbabilityTheory.BranchingRandomWalk

/-- Joint law of the actual rank-installed endpoint positions and their
fresh first-`N` BRW descendant field, restricted to finite first-success endpoints.
The position vector is measurable in the stopped domain filtration. The
fresh field has the independent `Fin lower` product law. Consequently this
identity gives the input law for every measurable fixed-horizon observable
of the retained positions and fresh field. -/
theorem selectedReserveSpineRestartEndpointPositionFreshField_jointLaw_on_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (hpositions : Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace] positions) :
    let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let futureLaw := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    (P.restrict {field | τ field ≠ ⊤}).map
        (fun field => (positions field,
          RootIndexed.selectedSubtreeStepFieldVector
            (fun field i => (Sum.inr r,
              (selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
                R growth hR hgrowth lower upper duration r field i).2)) field)) =
      ((P.restrict {field | τ field ≠ ⊤}).map positions).prod futureLaw := by
  classical
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hτ := selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ) := {field | τ field ≠ ⊤}
  let nSelectedBRWEndpointRankVector := selectedReserveSpineRestartNSelectedBRWEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let roots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    (Sum.inr r, (nSelectedBRWEndpointRankVector field i).2)
  let fresh := fun field => RootIndexed.selectedSubtreeStepFieldVector roots field
  have hsumSingleton : ∀ z : Root ⊕ Root,
      MeasurableSet ({z} : Set (Root ⊕ Root)) := by
    intro z
    cases z with
    | inl x =>
        rw [show ({Sum.inl x} : Set (Root ⊕ Root)) =
          Sum.inl '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inl_image
    | inr x =>
        rw [show ({Sum.inr x} : Set (Root ⊕ Root)) =
          Sum.inr '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inr_image
  letI : MeasurableSingletonClass (Root ⊕ Root) := ⟨hsumSingleton⟩
  have hτmeas : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)) τ := by
    simpa [τ] using hτ
  have hnSelectedBRWEndpointRankVector : Measurable[hτmeas.measurableSpace] nSelectedBRWEndpointRankVector := by
    simpa [nSelectedBRWEndpointRankVector, hτmeas] using
      selectedReserveSpineRestartNSelectedBRWEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hnSelectedBRWRootsStopped : Measurable[hτmeas.measurableSpace] roots := by
    letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
      hτmeas.measurableSpace
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable[hτmeas.measurableSpace] (fun field => nSelectedBRWEndpointRankVector field i) :=
      (measurable_pi_apply i).comp hnSelectedBRWEndpointRankVector
    have hpath := hnodePath.comp hi
    exact measurable_const.prodMk hpath
  have hrootsFull : Measurable roots := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hnSelectedBRWRootsStopped.mono hle le_rfl
  have hcount : (Set.range roots).Countable := by
    let encode : (Fin lower → RootIndexed.TreeNode Root α) →
        Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
      fun v i => (Sum.inr r, (v i).2)
    have hsubset : Set.range roots ⊆ Set.range encode := by
      rintro q ⟨field, rfl⟩
      exact ⟨nSelectedBRWEndpointRankVector field, rfl⟩
    exact (Set.countable_range encode).mono hsubset
  have hfresh : Measurable fresh := by
    change Measurable (fun field => RootIndexed.subtreeStepFieldVector
      (roots field) field)
    exact RootIndexed.subtreeStepFieldVector_measurable_of_measurable_roots roots hrootsFull hcount
  have hpositionsFull : Measurable positions := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hpositions.mono hle le_rfl
  have hpair : Measurable (fun field => (positions field, fresh field)) :=
    hpositionsFull.prodMk hfresh
  have hE : MeasurableSet E := by
    have htop : MeasurableSet[hτmeas.measurableSpace] {field | τ field = ⊤} :=
      hτmeas.measurable (measurableSet_singleton (⊤ : WithTop ℕ))
    have htopFull : MeasurableSet[⨆ n : ℕ,
        RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
        {field | τ field = ⊤}ᶜ := htop.compl.1
    have hle : (⨆ n : ℕ,
        RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ) n) ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le' n
    exact hle E htopFull
  have hleftFinite : IsFiniteMeasure ((P.restrict E).map
      (fun field => (positions field, fresh field))) := by infer_instance
  have hrect : ∀ {S : Set (Fin lower → ℝ)} {T : Set (Fin lower →
      Combinatorics.UlamHarris.TreeNode α → Step α ℝ)},
      MeasurableSet S → MeasurableSet T →
      ((P.restrict E).map (fun field => (positions field, fresh field)))
          (S ×ˢ T) =
        (((P.restrict E).map positions).prod Q) (S ×ˢ T) := by
    intro S T hS hT
    rw [Measure.map_apply hpair (hS.prod hT)]
    have hA : MeasurableSet[hτmeas.measurableSpace] (positions ⁻¹' S) :=
      hpositions hS
    have hfactor := selectedReserveSpineRestartNSelectedBRWFreshField_factorization_on_finite
      hnodePath μ hnorm N initialPosition R growth hR hgrowth lower upper duration
      hupper hbounded hcapacity r (positions ⁻¹' S) T hA hT
    rw [show (positions ⁻¹' S ∩ E) ∩ fresh ⁻¹' T =
        E ∩ positions ⁻¹' S ∩ fresh ⁻¹' T by
      ext field
      simp [and_assoc, and_left_comm, and_comm]] at hfactor
    rw [Measure.restrict_apply (hpair (hS.prod hT))]
    rw [show (fun field => (positions field, fresh field)) ⁻¹' (S ×ˢ T) =
        positions ⁻¹' S ∩ fresh ⁻¹' T by
      ext field
      simp]
    rw [Measure.prod_prod, Measure.map_apply hpositionsFull hS,
      Measure.restrict_apply (hpositionsFull hS)]
    simpa [P, Q, E, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hfactor
  have hjoint :
      (P.restrict E).map (fun field => (positions field, fresh field)) =
        ((P.restrict E).map positions).prod Q :=
    Measure.ext_prod hrect
  simpa [τ, P, Q, E, fresh, roots] using hjoint


end ProbabilityTheory.BranchingRandomWalk
