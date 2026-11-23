/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Continuation
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.EndpointExpectation
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Combinatorics.UlamHarris.Order

/-!
# Single-root block comparison

## Internal proof declarations

* `integral_selectedEndpoint_add_le_singleRoot`: fresh branching from a
  particle at the current minimum gives
  $\mathbb E[M_{n+H}]\le \mathbb E[M_n]+\mathbb E[M_H^{N|0}]$.

This is the mean comparison corresponding to the single-root blocks in
* `speed_le_integral_singleRootEndpoint_div`: writing $v_N$ for the $L^1$
  speed, the block recursion gives $v_Nlemathbb E[M_H^{N|0}]/H$.

Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Theorem 1.2.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris

noncomputable local instance blockUpperAddressOrder (s : ℕ) :
    LinearOrder (RootIndexed.TreeNode (Fin s) ℕ) :=
  RootIndexed.addressLinearOrder (Fin s) ℕ

open scoped ENNReal Topology

/-- At each block start, retain a particle at the current minimum. Its
translated fresh continuation bounds the conditional endpoint mean. -/
lemma integral_selectedEndpoint_add_le_singleRoot
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    (n H : ℕ) :
    let P := RootIndexed.stepFieldLaw (Root := Fin N) μ
    let F k := fun ω => RootIndexed.selectedPopulationEndpointWithParameter N N k
      ((fun _ => 0), ω)
    let Q := RootIndexed.stepFieldLaw (Root := Fin 1) μ
    let G := fun ω => RootIndexed.selectedPopulationEndpointWithParameter 1 N H
      ((fun _ => 0), ω)
    Integrable (F n) P → Integrable (F (n + H)) P → Integrable G Q →
    (∫ ω, F (n + H) ω ∂P) ≤ (∫ ω, F n ω ∂P) + ∫ ω, G ω ∂Q := by
  intro P F Q G hn hnext hG
  classical
  let b := ∫ ω, G ω ∂Q
  let pop := fun ω => RootIndexed.selectedPopulationWithParameter N N n ((fun _ => 0), ω)
  let I := Finset (RootIndexed.TreeNode (Fin N) ℕ)
  let A (S : I) := {ω | pop ω = S}
  have hpop : Measurable pop :=
    (RootIndexed.measurable_selectedPopulationWithParameter N N n).comp
      (measurable_const.prodMk measurable_id)
  have hA (S : I) : MeasurableSet (A S) := hpop (measurableSet_singleton _)
  have hd : Pairwise (fun S T => Disjoint (A S) (A T)) := by
    intro S T hST
    exact Set.disjoint_left.mpr fun ω hS hT => hST (hS.symm.trans hT)
  have hU : (⋃ S, A S) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨pop ω, rfl⟩
  have hcell (S : I) : (∫ ω in A S, F (n + H) ω ∂P) ≤ ∫ ω in A S, F n ω + b ∂P := by
    have hall : ∀ᵐ ω ∂P, (pop ω).Nonempty := by
      filter_upwards [RootIndexed.selectedPopulationTotalized_nonempty_ae N
        (Finset.univ : Finset (Fin N)) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
        (fun _ => 0) hN μ hboundary hne] with ω hω
      exact hω n
    by_cases hS : S.Nonempty
    swap
    · have hnull : P (A S) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hall] with ω hω hmem
        apply hS
        exact hmem ▸ hω
      simp [Measure.restrict_eq_zero.mpr hnull]
    obtain ⟨roots, hmap⟩ :=
      Function.Embedding.exists_of_card_eq_finset (α := Fin S.card) (s := S) (by simp)
    have hcover : Finset.univ.image roots = S := by
      rw [← Finset.map_eq_image]
      exact hmap
    by_cases hdepth : ∀ i, (roots i).2.length = n
    swap
    · have hnil : A S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        apply hdepth
        intro i
        have hi : roots i ∈ pop ω := by
          have hmem : roots i ∈ Finset.univ.image roots :=
            Finset.mem_image_of_mem _ (Finset.mem_univ i)
          exact (congrArg (fun pop => roots i ∈ pop) (hcover.trans hω.symm)).mp hmem
        exact RootIndexed.selectedPopulationTotalized_depth N Finset.univ
          (fun _ => (0 : ℝ)) id id n ω (roots i) hi
      simp [hnil]
    let embed (p : RootIndexed.TreeNode (Fin S.card) ℕ) : RootIndexed.TreeNode (Fin N) ℕ :=
      ((roots p.1).1, (roots p.1).2 ++ p.2)
    let sOrder := LinearOrder.lift' embed
      (Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective roots hdepth roots.injective)
    let _ : LinearOrder (RootIndexed.TreeNode (Fin S.card) ℕ) := sOrder
    let X := fun ω => RootIndexed.subtreeInitialPosition (fun _ => (0 : ℝ)) id ω roots
    let V := RootIndexed.subtreeStepFieldVector (X := ℝ) roots
    let ν := (P.restrict (A S)).map X
    let R := RootIndexed.stepFieldLaw (Root := Fin S.card) μ
    have hlocal := @RootIndexed.selectedEndpoint_continuation_on_cell N S.card
      (blockUpperAddressOrder N) sOrder μ _ N (fun _ => 0) n roots hdepth (fun _ _ => Iff.rfl)
    obtain ⟨_, hX, hV, hlaw, hpoint⟩ := hlocal
    rw [hcover] at hlaw hpoint
    have hm : (Finset.univ : Finset (Fin S.card)).Nonempty :=
      ⟨⟨0, Finset.card_pos.mpr hS⟩, Finset.mem_univ _⟩
    let c (x : Fin S.card → ℝ) := (Finset.univ : Finset (Fin S.card)).inf' hm x
    let f (z : (Fin S.card → ℝ) × RootIndexed.StepField (Fin S.card) ℕ ℝ) :=
      RootIndexed.selectedPopulationEndpointWithParameter S.card N H z
    have hf : Measurable f := RootIndexed.measurable_selectedPopulationEndpointWithParameter _ _ _
    have hc : Measurable c := by
      apply measurable_of_Ioi
      intro z
      simpa only [Set.preimage, Set.mem_Ioi, c, Finset.lt_inf'_iff, Finset.mem_univ, true_implies,
        Set.ofPred_forall] using
        (MeasurableSet.iInter fun i : Fin S.card => measurable_pi_apply i (measurableSet_Ioi (a := z)))
    have heq : (fun ω => f (X ω, V ω)) =ᵐ[P.restrict (A S)] F (n + H) := by
      filter_upwards [ae_restrict_mem (hA S)] with ω hω
      exact (hpoint ω hω H).symm
    have hmin : (fun ω => c (X ω)) =ᵐ[P.restrict (A S)] F n := by
      filter_upwards [ae_restrict_mem (hA S)] with ω hω
      simpa only [Nat.add_zero, RootIndexed.selectedPopulationEndpointWithParameter_zero_eq_inf
        N _ _ hm] using (hpoint ω hω 0).symm
    have hfi : Integrable f (ν.prod R) := by
      rw [← hlaw]
      exact (integrable_map_measure hf.aestronglyMeasurable
        (hX.prodMk hV).aemeasurable).mpr (hnext.integrableOn.congr heq.symm)
    have hci : Integrable c ν :=
      (integrable_map_measure hc.aestronglyMeasurable hX.aemeasurable).mpr
        (hn.integrableOn.congr hmin.symm)
    have hle : ∀ᵐ x ∂ν, (∫ ω, f (x, ω) ∂R) ≤ c x + b := by
      filter_upwards [hfi.prod_right_ae] with x hx
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' hm x
      let e : Fin 1 ↪ Fin S.card := ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
      exact RootIndexed.integral_selectedPopulationEndpointWithParameter_le_add_of_embedding
        μ hboundary hne N H hN (by decide) hN x e (c x) (fun _ => hi.ge) hx hG
    calc
      _ = ∫ z, f z ∂ν.prod R := by
        rw [← hlaw, integral_map (hX.prodMk hV).aemeasurable hf.aestronglyMeasurable]
        exact integral_congr_ae heq.symm
      _ = ∫ x, ∫ ω, f (x, ω) ∂R ∂ν := integral_prod f hfi
      _ ≤ ∫ x, c x + b ∂ν :=
        integral_mono_ae hfi.integral_prod_left (hci.add (integrable_const _)) hle
      _ = _ := by
        rw [integral_map hX.aemeasurable (hc.add_const b).aestronglyMeasurable]
        exact integral_congr_ae (hmin.mono fun ω hω => congrArg (· + b) hω)
  have hi : Integrable (fun ω => F n ω + b) P := hn.add (integrable_const _)
  have hmean : (∫ ω, F n ω + b ∂P) = (∫ ω, F n ω ∂P) + b := by
    rw [integral_add hn (integrable_const b), integral_const, probReal_univ, one_smul]
  change (∫ ω, F (n + H) ω ∂P) ≤ (∫ ω, F n ω ∂P) + b
  rw [← hmean]
  have hnextSum := hasSum_integral_iUnion hA hd hnext.integrableOn
  have hiSum := hasSum_integral_iUnion hA hd hi.integrableOn
  rw [hU, setIntegral_univ] at hnextSum hiSum
  rw [← hnextSum.tsum_eq, ← hiSum.tsum_eq]
  exact Summable.tsum_le_tsum hcell hnextSum.summable hiSum.summable

/-- Iterate the single-root comparison at block times and pass to the
(L^1) speed limit. -/
lemma speed_le_integral_singleRootEndpoint_div
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    (speed : ℝ) :
    let P := RootIndexed.stepFieldLaw (Root := Fin N) μ
    let F k := fun ω => RootIndexed.selectedPopulationEndpointWithParameter N N k
      ((fun _ => 0), ω)
    let Q := RootIndexed.stepFieldLaw (Root := Fin 1) μ
    let G := fun ω => RootIndexed.selectedPopulationEndpointWithParameter 1 N H
      ((fun _ => 0), ω)
    (∀ n, Integrable (F n) P) → Integrable G Q →
    Tendsto (fun n : ℕ => eLpNorm (fun ω => (n : ℝ)⁻¹ * F n ω - speed) 1 P)
      atTop (𝓝 0) →
    speed ≤ (∫ ω, G ω ∂Q) / H := by
  intro P F Q G hF hG hL1
  let b := ∫ ω, G ω ∂Q
  let u n := ∫ ω, F n ω ∂P
  have hzero : u 0 = 0 := by
    have heq (ω : RootIndexed.StepField (Fin N) ℕ ℝ) : F 0 ω = 0 := by
      have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
        ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      rw [show F 0 ω = RootIndexed.selectedPopulationEndpointWithParameter N N 0
        ((fun _ => 0), ω) from rfl,
        RootIndexed.selectedPopulationEndpointWithParameter_zero_eq_inf N _ _ hne]
      simp
    simp [u, heq]
  have hblock (k : ℕ) : u (k * H) ≤ (k : ℝ) * b := by
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
      rw [Nat.succ_mul, Nat.cast_succ, add_mul, one_mul]
      exact (integral_selectedEndpoint_add_le_singleRoot hN μ hboundary hne
        (k * H) H (hF _) (hF _) hG).trans (add_le_add ih le_rfl)
  have hnorm : Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 speed) := by
    have hl := tendsto_integral_of_L1' (μ := P) (fun _ => speed)
      (Eventually.of_forall fun n => (hF n).const_mul ((n : ℝ)⁻¹)) hL1
    simpa only [integral_const_mul, integral_const, probReal_univ, one_smul,
      div_eq_inv_mul, u] using hl
  have hmul : Tendsto (fun k : ℕ => k * H) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    exact (eventually_ge_atTop k).mono fun n hn => hn.trans (Nat.le_mul_of_pos_right _ hH)
  apply le_of_tendsto (hnorm.comp hmul)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  change u (k * H) / ((k * H : ℕ) : ℝ) ≤ b / H
  rw [Nat.cast_mul]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ (k : ℝ) * b / ((k : ℝ) * H) := div_le_div_of_nonneg_right (hblock k)
      (mul_pos hk' hH').le
    _ = b / H := by field_simp [hk'.ne', hH'.ne']

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
