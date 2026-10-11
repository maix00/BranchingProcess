/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Generation
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.DomainFlow
public import Combinatorics.BranchingWalk.Basic.Map
public import Combinatorics.BranchingWalk.StepField

import Mathlib.Probability.Independence.Integration

/-!
# First-generation branching decomposition

The root step and each child descendant field have their product law under the
pre-sampled i.i.d. step field. The generation-address equivalence records the
deterministic decomposition of generation `n + 1` into a first child slot and
a generation-`n` address inside that child's subtree.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Generation `n + 1` addresses are a first slot followed by a generation
`n` address. No distinguished or default slot is chosen. -/
def generationConsEquiv (ι : Type*) (n : ℕ) :
    ι × {v : TreeNode ι // v.length = n} ≃
      {u : TreeNode ι // u.length = n + 1} where
  toFun p := ⟨p.1 :: p.2.1, by simp [p.2.2]⟩
  invFun u := by
    have hpos : 0 < u.1.length := by omega
    have hne : u.1 ≠ [] := List.ne_nil_of_length_pos hpos
    exact (u.1.head hne, ⟨u.1.tail, by simp [List.length_tail, u.2]⟩)
  left_inv p := by
    rcases p with ⟨i, v⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp
  right_inv u := by
    apply Subtype.ext
    exact List.cons_head_tail
      (List.ne_nil_of_length_pos (by omega : 0 < u.1.length))

/-- The root reproduction step and the complete descendant step field below
any one child have the product of their marginal laws. -/
theorem root_subtreeStepField_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (i : ι) :
    (stepFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι), subtreeStepField [i] ω)) =
      μ.prod (stepFieldLaw μ) := by
  have hrootPast : Measurable[generationFiltration
      (M := Combinatorics.Branching.Step ι X) 1]
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι)) :=
    mark_measurable_of_depth_lt [] 1 (by simp)
  have hind : IndepFun
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι))
      (subtreeStepField (X := X) [i]) (stepFieldLaw μ) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (generation_subtreeStepField_independent μ [i]) hrootPast.comap_le
  rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply ([] : TreeNode ι)).aemeasurable
      (subtreeStepField_measurable [i]).aemeasurable,
    stepFieldLaw_coordinate μ ([] : TreeNode ι),
    subtreeStepField_law μ [i]]

theorem pathPotential_cons
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : Combinatorics.Branching.StepField ι X)
    (i : ι) (v : TreeNode ι) :
    pathPotential φ ω (i :: v) =
      (ω []).potentialValue' φ i +
        pathPotential φ (subtreeStepField [i] ω) v := by
  rw [show i :: v = [i] ++ v from rfl]
  unfold pathPotential displaceWith
  rw [subtreeStepField_position_decomposition (ω.map φ) [i] v]
  have hmap : subtreeStepField [i] (ω.map φ) =
      Combinatorics.Branching.StepField.map φ
        (subtreeStepField [i] ω) := rfl
  rw [hmap]
  simp [displace, Combinatorics.Branching.StepField.map_apply,
    Step.potentialValue', Step.potentialAt?, value']

/-- Integrating an observable of the root step and a fixed child's subtree
uses their product law. -/
theorem lintegral_root_subtreeFunction_eq
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i : ι) (H : Step ι X × StepField ι X → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ ω, H (ω ([] : TreeNode ι), subtreeStepField [i] ω)
      ∂stepFieldLaw μ) =
      ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂stepFieldLaw μ ∂μ := by
  let pair : StepField ι X → Step ι X × StepField ι X := fun ω =>
    (ω [], subtreeStepField [i] ω)
  have hpair : Measurable pair :=
    (measurable_pi_apply ([] : TreeNode ι)).prodMk
      (subtreeStepField_measurable [i])
  calc
    (∫⁻ ω, H (ω ([] : TreeNode ι), subtreeStepField [i] ω)
        ∂stepFieldLaw μ) = ∫⁻ z, H z ∂(stepFieldLaw μ).map pair := by
      exact (lintegral_map hH hpair).symm
    _ = ∫⁻ z, H z ∂μ.prod (stepFieldLaw μ) := by
      rw [root_subtreeStepField_joint_law μ i]
    _ = ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂stepFieldLaw μ ∂μ :=
      lintegral_prod H hH.aemeasurable


/-- An observable of the reproduction mark at a generation-`n` frontier is
independent of every measurable generation-`n` prefix observable.  The exact
factorization lets positive-depth MRCA terms be estimated by first bounding
the continuation observable at a fixed ancestor, then integrating its mark
against the original offspring law. -/
theorem lintegral_generationPrefixObservableSum_eq_mul
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞)
    (g : Step ℕ X → ℝ≥0∞)
    (hAgen : ∀ u, Measurable[generationFiltration (M := Step ℕ X) n]
      (A u))
    (hA : ∀ u, Measurable (A u))
    (hsupport : ∀ u, u.length ≠ n → A u = fun _ => 0)
    (hg : Measurable g) :
    (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * g (ω u)
      ∂stepFieldLaw μ) =
        (∫⁻ ξ, g ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) := by
  classical
  let B (u : TreeNode ℕ) : StepField ℕ X → ℝ≥0∞ :=
    fun ω => g (ω u)
  have hBgen (u : TreeNode ℕ) :
      Measurable[MeasurableSpace.comap (subtreeStepField u) inferInstance]
        (B u) := by
    have hroot : Measurable (fun η : StepField ℕ X => g (η [])) :=
      hg.comp (measurable_pi_apply ([] : TreeNode ℕ))
    apply Measurable.of_comap_le
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (f := subtreeStepField u) (g := B u)
      (h := fun η : StepField ℕ X => g (η [])) hroot (by
        funext ω
        simp [B, subtreeStepField])
  have hfactor (u : TreeNode ℕ) :
      (∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ) =
        (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
          (∫⁻ ξ, g ξ ∂μ) := by
    by_cases hu : u.length = n
    · subst n
      have hind : IndepFun (A u) (B u) (stepFieldLaw μ) := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_right
          (indep_of_indep_of_le_left
            (generation_subtreeStepField_independent μ u) (hAgen u).comap_le)
          (hBgen u).comap_le
      calc
        (∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ) =
            (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
              (∫⁻ ξ, B u ξ ∂stepFieldLaw μ) :=
          lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
            (hA u) (hg.comp (measurable_pi_apply u)) hind
        _ = (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
              (∫⁻ ξ, g ξ ∂μ) := by
          congr 1
          change (∫⁻ ω, g (ω u) ∂stepFieldLaw μ) = _
          calc
            _ = ∫⁻ ξ, g ξ ∂(stepFieldLaw μ).map
                (fun ω : StepField ℕ X => ω u) := by
              exact (lintegral_map hg
                (measurable_pi_apply u :
                  Measurable (fun ω : StepField ℕ X => ω u))).symm
            _ = ∫⁻ ξ, g ξ ∂μ := by
              rw [stepFieldLaw_coordinate μ u]
    · have hzero : A u = fun _ => 0 := hsupport u hu
      simp [hzero]
  have htermMeas (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X => A u ω * B u ω) :=
    (hA u).mul (hg.comp (measurable_pi_apply u))
  have hsumIntegral :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (htermMeas u).aemeasurable
  have hprefix :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ, ∫⁻ ω, A u ω ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (hA u).aemeasurable
  calc
    (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * g (ω u)
        ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂stepFieldLaw μ := by
      change (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω
        ∂stepFieldLaw μ) = _
      exact hsumIntegral
    _ = ∑' u : TreeNode ℕ,
          (∫⁻ ω, A u ω ∂stepFieldLaw μ) *
            (∫⁻ ξ, g ξ ∂μ) := by
      apply tsum_congr
      intro u
      exact hfactor u
    _ = (∫⁻ ξ, g ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂stepFieldLaw μ) := by
      rw [ENNReal.tsum_mul_right, hprefix, mul_comm]

end ProbabilityTheory.BranchingRandomWalk.Spine
