/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.FirstMoment
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Population
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Overflow
import Probability.Independence.Integration.Basic
import MeasureTheory.Integral.MeasurePreserving

/-!
# Positive endpoint bound from two lineages

## Internal proof declarations

* `finiteRootStepFieldLaw_endpointMinimum_pos_sq_le`: if the initial cloud
  has at least two origins and the selection capacity is at least two, then
  $\mathbb E[(M_H)_+^2]\le H^2(\mathbb E|D|)^2$, where $D$ is the leftmost
  displacement. The two lineages in distinct initial root fields are used
  only to bound the positive tail. The endpoint is the original selected
  endpoint under its product field law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Coupling

private abbrev zeroAddress (n : ℕ) : TreeNode ℕ := List.replicate n 0

private lemma zeroAddress_succ (n : ℕ) :
    zeroAddress (n + 1) = zeroAddress n ++ [0] := by
  rw [show [0] = zeroAddress 1 from rfl, List.replicate_append_replicate]

private def twoLineageSlice {Root : Type*} (roots : Finset Root)
    (n : ℕ) (field : RootIndexed.StepField Root ℕ ℝ) :
    Set (RootIndexed.TreeNode Root ℕ) :=
  {p | p.1 ∈ roots ∧ p.2 = zeroAddress n ∧
    ∀ j < n, survive (field p.1 (zeroAddress j)) 0}

private def twoLineagePopulation {Root : Type*} (roots : Finset Root) :
    RootIndexed.CausalPopulation (RootIndexed.StepField (Root ⊕ Root) ℕ ℝ) Root ℕ ℝ
      RootIndexed.stepFiltration RootIndexed.StepField.left where
  toPopulation field :=
    { particles := fun n => twoLineageSlice roots n (RootIndexed.StepField.left field)
      depth := fun n p hp => by
        change _ ∧ p.2 = zeroAddress n ∧ _ at hp
        simp [hp.2.1]
      successor := fun n p hp => by
        change _ ∧ p.2 = zeroAddress (n + 1) ∧ _ at hp
        rcases hp with ⟨hr, hp, hmarks⟩
        refine Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
          ⟨(p.1, zeroAddress n), ⟨hr, rfl, fun j hj => hmarks j (by omega)⟩,
            0, hmarks n (Nat.lt_succ_self n), ?_⟩
        exact Prod.ext rfl (hp.trans (zeroAddress_succ _)) }
  adapted p n := by
    apply measurable_to_prop
    simp only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
      twoLineageSlice]
    change MeasurableSet[RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := ℕ) (X := ℝ) n]
      {field | p.1 ∈ roots ∧ p.2 = zeroAddress n ∧
        ∀ j < n, survive (RootIndexed.StepField.left field p.1 (zeroAddress j)) 0}
    classical
    rw [show {field : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ |
        p.1 ∈ roots ∧ p.2 = zeroAddress n ∧
          ∀ j < n, survive (RootIndexed.StepField.left field p.1 (zeroAddress j)) 0} =
        { _field : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ | p.1 ∈ roots ∧ p.2 = zeroAddress n} ∩
          ⋂ j : Fin n, {field | survive (field (Sum.inl p.1) (zeroAddress j)) 0} by
      ext field
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, and_assoc]
      exact and_congr_right fun _ => and_congr_right fun _ =>
        ⟨fun h j => h j j.isLt, fun h j hj => h ⟨j, hj⟩⟩]
    apply MeasurableSet.inter
    · by_cases h : p.1 ∈ roots ∧ p.2 = zeroAddress n <;> simp [h]
    apply MeasurableSet.iInter
    intro j
    exact RootIndexed.step_measurable (Sum.inl p.1 : Root ⊕ Root) (zeroAddress j)
      (by simp) (survive_measurableSet 0)

private theorem lineagesFinite {Root : Type*} (roots : Finset Root) :
    (twoLineagePopulation roots).FiniteSlices := by
  intro n field
  exact (roots.finite_toSet.image (fun r => (r, zeroAddress n))).subset
    (fun p hp => ⟨p.1, hp.1, Prod.ext rfl hp.2.1.symm⟩)

private def absDisplacementSum (H : ℕ) (field : Mark ℕ (Step ℕ ℝ)) : ℝ :=
  ∑ j ∈ Finset.range H, |value' (field (zeroAddress j)) 0|

private theorem position_zeroAddress_le {Root : Type*}
    (field : RootIndexed.StepField Root ℕ ℝ) (r : Root) (H : ℕ) :
    RootIndexed.position (fun _ => (0 : ℝ)) id field r (zeroAddress H) ≤
      absDisplacementSum H (field r) := by
  induction H with
  | zero => simp [absDisplacementSum, RootIndexed.position]
  | succ H ih =>
    rw [show zeroAddress (H + 1) = zeroAddress H ++ [0] from
      zeroAddress_succ _, RootIndexed.position_append_singleton]
    unfold absDisplacementSum
    rw [Finset.sum_range_succ]
    simpa [absDisplacementSum] using add_le_add ih (le_abs_self (value' (field r (zeroAddress H)) 0))

set_option maxHeartbeats 1000000 in
lemma finiteRootStepFieldLaw_endpointMinimum_pos_sq_le
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hnorm : HasBoundaryNormalization L.potential L.raw)
    (hne : L.raw nonemptySupport = 1) (hfirst : HasLeftmostFirstMoment L)
    (m N H : ℕ) (hm : 2 ≤ m) (hN : 2 ≤ N)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    let P := finiteRootStepFieldLaw L.sortedPotentialImage m
    let F := firstNSelectedEndpointMinimum m N H
    Integrable (fun ω => (max (F ω) 0) ^ 2) P ∧
      (∫ ω, (max (F ω) 0) ^ 2 ∂P) ≤
        ((H : ℝ) * ∫ ξ, |value' ξ 0| ∂L.sortedPotentialImage) ^ 2 := by
  classical
  intro P F
  let Root := Fin m
  let μ := L.sortedPotentialImage
  let Q := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let r₀ : Root := ⟨0, by omega⟩
  let r₁ : Root := ⟨1, by omega⟩
  have hneRoots : r₀ ≠ r₁ := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  let roots : Finset Root := {r₀, r₁}
  let S := twoLineagePopulation roots
  let hS := lineagesFinite roots
  let pop := hS.toFinset
  let initial : Root → ℝ := fun _ => 0
  have hinit (field : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ) :
      Cloud.SliceDominatingMap id
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initial (RootIndexed.StepField.left field))
          (pop 0 field))
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initial (RootIndexed.StepField.right field))
          (RootIndexed.restartedRealPositionNSelectedBRWPopulation N Finset.univ initial id pop 0 field)) () := by
    refine ⟨id, ?_, Set.injOn_id _, ?_⟩
    · intro p hp
      change p ∈ pop 0 field at hp
      rw [RootIndexed.CausalPopulation.FiniteSlices.mem_toFinset] at hp
      change _ ∧ p.2 = [] ∧ _ at hp
      change p ∈ RootIndexed.initialPopulation Finset.univ
      exact RootIndexed.mem_initialPopulation_iff.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl hp.2.1⟩
    · intro p hp
      change p ∈ pop 0 field at hp
      rw [RootIndexed.CausalPopulation.FiniteSlices.mem_toFinset] at hp
      change _ ∧ p.2 = [] ∧ _ at hp
      change RootIndexed.position initial id (RootIndexed.StepField.right field) p.1 p.2 ≤
        RootIndexed.position initial id (RootIndexed.StepField.left field) p.1 p.2
      rw [hp.2.1]
      simp [RootIndexed.position]
  obtain ⟨hV, hmap, -, -, hcomp⟩ :=
    RootIndexed.restartedRealPositionComparison_throughOverflow_ae μ
      N (by omega) (Finset.univ : Finset Root) initial
      (@RootIndexed.selectedPopulationTotalized_admissible_ae Root ℕ inferInstance
        LinearOrder.toDecidableEq inferInstance μ inferInstance
        (L.sortedPotentialImage_hasBoundaryNormalization hnorm) N Finset.univ initial) S hS hinit
  let V := RootIndexed.restartedRealPositionTrajectoryField N (Finset.univ : Finset Root)
    initial id pop
  have hcard (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ) :
      (pop n field).card ≤ N := by
    have hs : pop n field ⊆ roots.image (fun r => (r, zeroAddress n)) := by
      intro p hp
      rw [RootIndexed.CausalPopulation.FiniteSlices.mem_toFinset] at hp
      exact Finset.mem_image.mpr ⟨p.1, hp.1, Prod.ext rfl hp.2.1.symm⟩
    exact (Finset.card_le_card hs).trans
      (Finset.card_image_le.trans (by simpa [roots, hneRoots] using hN))
  have hμne : μ nonemptySupport = 1 := by
    change L.sortedPotentialImage nonemptySupport = 1
    rwa [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
  have hord : μ orderedSteps = 1 := by
    rw [show orderedSteps = orderedBySteps realPotential by
      ext ξ; simp [orderedBySteps, Step.IsOrderedBy, realPotential]]
    rw [L.sortedPotentialImage_orderedBy]
    simp
  have hslot : ∀ᵐ field ∂Q, ∀ r u, survive (field r u) 0 := by
    filter_upwards [RootIndexed.stepFieldLaw_ae_all_of_measure_one
      (Root := Root ⊕ Root) orderedSteps_measurable μ hord,
      RootIndexed.stepFieldLaw_ae_all_of_measure_one
      (Root := Root ⊕ Root) nonemptySupport_measurable μ hμne] with field ho hs r u
    obtain ⟨j, hj⟩ := hs r u
    exact orderedSteps_survive_of_le (field r u) (ho r u) (Nat.zero_le _) hj
  let W (r : Root) (field : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ) :=
    absDisplacementSum H (field (Sum.inl r))
  have hdom : ∀ᵐ field ∂Q, (max (F (V field)) 0)^2 ≤ W r₀ field * W r₁ field := by
    filter_upwards [hcomp, hslot] with field hcompare hs
    have htime : (H : WithTop ℕ) ≤ finsetPopulationOverflowTime pop N field := by
      apply (lt_of_not_ge ?_).le
      intro h
      obtain ⟨j, -, hj⟩ := (finsetPopulationOverflowTime_le_iff pop N H field).1 h
      exact (not_lt_of_ge (hcard j field)) hj
    have hInf := (hcompare H).2 htime
    have hle (r : Root) (hr : r ∈ roots) : F (V field) ≤ W r field := by
      have hmem : (r, zeroAddress H) ∈ pop H field :=
        (RootIndexed.CausalPopulation.FiniteSlices.mem_toFinset _ _ _ _).2
          ⟨hr, rfl, fun _ _ => hs _ _⟩
      have hle := hInf.trans (Finset.inf_le hmem)
      let selected := firstNSelectedPopulation m N H (V field)
      let pos (q : RootIndexed.TreeNode Root ℕ) :=
        RootIndexed.position initial id (V field) q.1 q.2
      let x := RootIndexed.position initial id (RootIndexed.StepField.left field) r (zeroAddress H)
      have hle' : selected.inf (fun q => (pos q : WithTop ℝ)) ≤ (x : WithTop ℝ) := by
        simp only [selected, firstNSelectedPopulation, pos, x, V, pop,
          RootIndexed.BranchingWalk.position, RootIndexed.BranchingWalk.ofStepField,
          RootIndexed.position, RootIndexed.displace, initial, Root] at hle ⊢
        convert hle using 3
      clear hle
      have hn : selected.Nonempty := by
        by_contra hn
        have hzero : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        rw [hzero, Finset.inf_empty] at hle'
        exact (not_le_of_gt (WithTop.coe_lt_top x)) hle'
      have hmin := firstNSelectedEndpointMinimum_eq_inf'_of_nonempty m N H (V field) hn
      have hlo : (F (V field) : WithTop ℝ) ≤ (x : WithTop ℝ) := by
        change (↑(firstNSelectedEndpointMinimum m N H (V field)) : WithTop ℝ) ≤ _
        rw [hmin]
        exact le_trans (Finset.le_inf fun q hq =>
          WithTop.coe_le_coe.mpr (Finset.inf'_le pos hq)) hle'
      exact (WithTop.coe_le_coe.mp hlo).trans
        (position_zeroAddress_le (RootIndexed.StepField.left field) r H)
    have h0 : 0 ≤ W r₀ field := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 : 0 ≤ W r₁ field := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [pow_two]
    exact mul_le_mul (max_le (hle r₀ (by simp [roots])) h0)
      (max_le (hle r₁ (by simp [roots])) h1) (le_max_right _ _) h0
  have hX := L.integrable_sortedPotentialImage_firstSlot_abs hnorm hfirst
  have hcoord (r : Root) (j : ℕ) :
      MeasurePreserving (fun field : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ =>
        field (Sum.inl r) (zeroAddress j)) Q μ :=
    ⟨(measurable_pi_apply _).comp (measurable_pi_apply _),
      RootIndexed.stepFieldLaw_coordinate_marginal μ (Sum.inl r) (zeroAddress j)⟩
  have hW (r : Root) : Integrable (W r) Q :=
    integrable_finsetSum _ fun j _ => (hcoord r j).integrable_comp_of_integrable hX
  have hmW (r : Root) :
      (∫ field, W r field ∂Q) = (H : ℝ) * ∫ ξ, |value' ξ 0| ∂μ := by
    change (∫ field, ∑ j ∈ Finset.range H,
      |value' (field (Sum.inl r) (zeroAddress j)) 0| ∂Q) = _
    have hint (j : ℕ) : Integrable
        (fun field : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ =>
          |value' (field (Sum.inl r) (zeroAddress j)) 0|) Q :=
      (hcoord r j).integrable_comp_of_integrable hX
    rw [integral_finsetSum _ (fun j _ => hint j)]
    have heq (j : ℕ) : (∫ field, |value' (field (Sum.inl r) (zeroAddress j)) 0| ∂Q) =
        ∫ ξ, |value' ξ 0| ∂μ := (hcoord r j).integral_comp_of_integrable hX
    simp [heq]
  have hmSum : Measurable (absDisplacementSum H) :=
    Finset.measurable_sum _ fun j _ => ((value'_measurable (0 : ℕ)).comp (measurable_pi_apply _)).abs
  have hind : IndepFun (W r₀) (W r₁) Q :=
    ((RootIndexed.stepFieldLaw_roots_independent (Root := Root ⊕ Root) μ).indepFun
      (i := Sum.inl r₀) (j := Sum.inl r₁) (by simpa using hneRoots)).comp hmSum hmSum
  have hprod := hind.integrable_mul (hW r₀) (hW r₁)
  let G (ω : RootIndexed.StepField Root ℕ ℝ) := (max (F ω) 0)^2
  have hg : Measurable G :=
    ((measurable_firstNSelectedEndpointMinimum m N H).max measurable_const).pow_const 2
  have hpres : MeasurePreserving V Q P := ⟨hV, hmap⟩
  have hG : Integrable (G ∘ V) Q := hprod.mono'
    (hg.comp hV).aestronglyMeasurable
    (hdom.mono fun field h => by
      change ‖(max (F (V field)) 0)^2‖ ≤ _
      rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
  have hGP : Integrable G P := hpres.integrable_comp hg.aestronglyMeasurable |>.1 hG
  refine ⟨hGP, ?_⟩
  calc
    _ = ∫ field, G (V field) ∂Q := (hpres.integral_comp_of_integrable hGP).symm
    _ ≤ ∫ field, W r₀ field * W r₁ field ∂Q := integral_mono_ae hG hprod hdom
    _ = _ := by
      rw [hind.integral_fun_mul_eq_mul_integral (hW r₀).aestronglyMeasurable
        (hW r₁).aestronglyMeasurable, hmW, hmW, pow_two]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
