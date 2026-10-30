/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Generation
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.AddressFiltration
public import Combinatorics.BranchingWalk.Basic.Map
public import Combinatorics.BranchingWalk.StepField

import Mathlib.Probability.Independence.Integration

/-!
# First-generation branching decomposition

The root step and each child descendant field have their product law under the
pre-sampled i.i.d. step field. The generation-address equivalence records the
deterministic decomposition of generation `n + 1` into a first child slot and
a generation-`n` address inside that child's subtree.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.Spine.generationConsEquiv` identifies
  generation-`n + 1` addresses with pairs `(i, v)` where `v` has length `n`:
  $\iota\times\{v : \mathrm{TreeNode}(\iota)\mid |v|=n\}\simeq
    \{u : \mathrm{TreeNode}(\iota)\mid |u|=n+1\}$.
- `ProbabilityTheory.BranchingRandomWalk.Spine.root_subtreeStepField_joint_law`
  states that the root step and the descendant field below a fixed child are
  independent, with
  $\mathcal L(\omega_{\varnothing},\omega_{[i]})
    =\mu\otimes\mathrm{offspringFieldLaw}(\mu)$.
- `ProbabilityTheory.BranchingRandomWalk.Spine.pathPotential_cons` gives the
  path-potential recursion
  $\mathrm{pathPotential}_{\varphi}(\omega,i::v)=
    (\omega_{\varnothing}).\mathrm{potentialValue}'_{\varphi}(i)+
    \mathrm{pathPotential}_{\varphi}(\omega_{[i]},v)$.
- `ProbabilityTheory.BranchingRandomWalk.Spine.pathPotential_append` splits
  the potential at any address prefix $u$:
  $\mathrm{pathPotential}_{\varphi}(\omega,u++v)=
    \mathrm{pathPotential}_{\varphi}(\omega,u)+
    \mathrm{pathPotential}_{\varphi}(\omega_u,v)$, where
  $\omega_u(w)=\omega(u++w)$.
- `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_root_subtreeFunction_eq`
  expresses the integral of a measurable `H` over the root/subtree pair as
  iterated integration against $\mu$ and `offspringFieldLaw μ`:
  $\int H(\omega_{\varnothing},\omega_{[i]})\,d\mathbb P(\omega)
    =\int\!\int H(\xi,\eta)\,d\mathrm{offspringFieldLaw}(\mu)(\eta)\,d\mu(\xi)$.
- `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_generationPrefixObservableSum_eq_mul`
  factors the integral of a generation-`n` prefix sum against a measurable
  frontier observable $g$ as
  $\int\!\sum_{|u|=n}A_u(\omega)g(\omega(u))\,d\mathbb P
    =(\int g\,d\mu)(\int\!\sum_{|u|=n}A_u\,d\mathbb P)$,
  when $g$ and each $A_u$ are measurable, each $A_u$ is generation-`n`
  measurable, and $A_u=0$ off that generation.
- `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_generationPrefixParameterizedObservableSum_eq`
  replaces a position-dependent frontier observable by its offspring-law
  mean inside the prefix integral:
  $\int\!\sum_{|u|=n}A_u(\omega)g(p_u(\omega),\omega(u))\,d\mathbb P
    =\int\!\sum_{|u|=n}A_u(\omega)
      (\int g(p_u(\omega),\xi)\,d\mu(\xi))\,d\mathbb P$,
  when, for each `u`, the prefix weight `A u` and position `p_u` are
  generation-`n` measurable, `A u=0` if $|u|\ne n$, and `g` is jointly
  measurable.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

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
    (offspringFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι), subtreeStepField [i] ω)) =
      μ.prod (offspringFieldLaw μ) := by
  have hrootPast : Measurable[generationFiltration
      (M := Combinatorics.Branching.Step ι X) 1]
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι)) :=
    mark_measurable_of_depth_lt [] 1 (by simp)
  have hind : IndepFun
      (fun ω : Combinatorics.Branching.StepField ι X =>
        ω ([] : TreeNode ι))
      (subtreeStepField (X := X) [i]) (offspringFieldLaw μ) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (generation_subtreeStepField_independent μ [i]) hrootPast.comap_le
  rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply ([] : TreeNode ι)).aemeasurable
      (subtreeStepField_measurable [i]).aemeasurable,
    offspringFieldLaw_coordinate μ ([] : TreeNode ι),
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

/-- Splitting an address into a prefix and a suffix splits its potential into
the prefix potential and the suffix potential in the subtree below the
prefix. -/
theorem pathPotential_append
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ω : Combinatorics.Branching.StepField ι X)
    (u v : TreeNode ι) :
    pathPotential φ ω (u ++ v) =
      pathPotential φ ω u + pathPotential φ (subtreeStepField u ω) v := by
  change displace (Combinatorics.Branching.StepField.map φ ω) [] (u ++ v) =
    displace (Combinatorics.Branching.StepField.map φ ω) [] u +
      displace (Combinatorics.Branching.StepField.map φ
        (subtreeStepField u ω)) [] v
  rw [subtreeStepField_position_decomposition
    (Combinatorics.Branching.StepField.map φ ω) u v]
  congr 1

/-- Integrating an observable of the root step and a fixed child's subtree
uses their product law. -/
theorem lintegral_root_subtreeFunction_eq
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i : ι) (H : Step ι X × StepField ι X → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ ω, H (ω ([] : TreeNode ι), subtreeStepField [i] ω)
      ∂offspringFieldLaw μ) =
      ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂offspringFieldLaw μ ∂μ := by
  let pair : StepField ι X → Step ι X × StepField ι X := fun ω =>
    (ω [], subtreeStepField [i] ω)
  have hpair : Measurable pair :=
    (measurable_pi_apply ([] : TreeNode ι)).prodMk
      (subtreeStepField_measurable [i])
  calc
    (∫⁻ ω, H (ω ([] : TreeNode ι), subtreeStepField [i] ω)
        ∂offspringFieldLaw μ) = ∫⁻ z, H z ∂(offspringFieldLaw μ).map pair := by
      exact (lintegral_map hH hpair).symm
    _ = ∫⁻ z, H z ∂μ.prod (offspringFieldLaw μ) := by
      rw [root_subtreeStepField_joint_law μ i]
    _ = ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂offspringFieldLaw μ ∂μ :=
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
      ∂offspringFieldLaw μ) =
        (∫⁻ ξ, g ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) := by
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
      (∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ) =
        (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
          (∫⁻ ξ, g ξ ∂μ) := by
    by_cases hu : u.length = n
    · subst n
      have hind : IndepFun (A u) (B u) (offspringFieldLaw μ) := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_right
          (indep_of_indep_of_le_left
            (generation_subtreeStepField_independent μ u) (hAgen u).comap_le)
          (hBgen u).comap_le
      calc
        (∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ) =
            (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
              (∫⁻ ξ, B u ξ ∂offspringFieldLaw μ) :=
          lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
            (hA u) (hg.comp (measurable_pi_apply u)) hind
        _ = (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
              (∫⁻ ξ, g ξ ∂μ) := by
          congr 1
          change (∫⁻ ω, g (ω u) ∂offspringFieldLaw μ) = _
          calc
            _ = ∫⁻ ξ, g ξ ∂(offspringFieldLaw μ).map
                (fun ω : StepField ℕ X => ω u) := by
              exact (lintegral_map hg
                (measurable_pi_apply u :
                  Measurable (fun ω : StepField ℕ X => ω u))).symm
            _ = ∫⁻ ξ, g ξ ∂μ := by
              rw [offspringFieldLaw_coordinate μ u]
    · have hzero : A u = fun _ => 0 := hsupport u hu
      simp [hzero]
  have htermMeas (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X => A u ω * B u ω) :=
    (hA u).mul (hg.comp (measurable_pi_apply u))
  have hsumIntegral :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω ∂offspringFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (htermMeas u).aemeasurable
  have hprefix :
      (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) =
        ∑' u : TreeNode ℕ, ∫⁻ ω, A u ω ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (hA u).aemeasurable
  calc
    (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * g (ω u)
        ∂offspringFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * B u ω ∂offspringFieldLaw μ := by
      change (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω * B u ω
        ∂offspringFieldLaw μ) = _
      exact hsumIntegral
    _ = ∑' u : TreeNode ℕ,
          (∫⁻ ω, A u ω ∂offspringFieldLaw μ) *
            (∫⁻ ξ, g ξ ∂μ) := by
      apply tsum_congr
      intro u
      exact hfactor u
    _ = (∫⁻ ξ, g ξ ∂μ) *
          (∫⁻ ω, ∑' u : TreeNode ℕ, A u ω ∂offspringFieldLaw μ) := by
      rw [ENNReal.tsum_mul_right, hprefix, mul_comm]

/-- Conditioning a generation-prefix term against the reproduction mark at
its frontier replaces a position-dependent frontier observable by its
offspring-law mean at that same ancestral position. -/
theorem lintegral_generationPrefixParameterizedObservableSum_eq
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞)
    (position : TreeNode ℕ → StepField ℕ X → ℝ)
    (g : ℝ → Step ℕ X → ℝ≥0∞)
    (hAgen : ∀ u, Measurable[generationFiltration (M := Step ℕ X) n]
      (A u))
    (hA : ∀ u, Measurable (A u))
    (hpositionGen : ∀ u,
      Measurable[generationFiltration (M := Step ℕ X) n]
        (position u))
    (hposition : ∀ u, Measurable (position u))
    (hsupport : ∀ u, u.length ≠ n → A u = fun _ => 0)
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ) =
      ∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
        ∂offspringFieldLaw μ := by
  classical
  have hmean : Measurable (fun x : ℝ => ∫⁻ ξ, g x ξ ∂μ) :=
    Measurable.lintegral_prod_right hg
  have htermLeft (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X =>
        A u ω * g (position u ω) (ω u)) := by
    exact (hA u).mul
      (hg.comp ((hposition u).prodMk (measurable_pi_apply u)))
  have htermRight (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X =>
        A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)) := by
    exact (hA u).mul (hmean.comp (hposition u))
  have hfactor (u : TreeNode ℕ) :
      (∫⁻ ω, A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ) =
      ∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
        ∂offspringFieldLaw μ := by
    by_cases hu : u.length = n
    · subst n
      let state : StepField ℕ X → ℝ≥0∞ × ℝ :=
        fun ω => (A u ω, position u ω)
      let mark : StepField ℕ X → Step ℕ X := fun ω => ω u
      let pair : StepField ℕ X → (ℝ≥0∞ × ℝ) × Step ℕ X :=
        fun ω => (state ω, mark ω)
      let H : (ℝ≥0∞ × ℝ) × Step ℕ X → ℝ≥0∞ :=
        fun p => p.1.1 * g p.1.2 p.2
      have hstateGen : Measurable[generationFiltration
          (M := Step ℕ X) u.length] state :=
        (hAgen u).prodMk (hpositionGen u)
      have hstate : Measurable state :=
        (hA u).prodMk (hposition u)
      have hmarkSubtree :
          Measurable[MeasurableSpace.comap (subtreeStepField u)
            inferInstance] mark := by
        apply Measurable.of_comap_le
        exact MeasurableSpace.comap_le_comap_of_eq_comp
          (f := subtreeStepField u) (g := mark)
          (h := fun η : StepField ℕ X => η [])
          (measurable_pi_apply ([] : TreeNode ℕ)) (by
            funext ω
            simp [mark, subtreeStepField])
      have hind : IndepFun state mark (offspringFieldLaw μ) := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_right
          (indep_of_indep_of_le_left
            (generation_subtreeStepField_independent μ u)
            hstateGen.comap_le)
          hmarkSubtree.comap_le
      have hpair : Measurable pair := hstate.prodMk
        (measurable_pi_apply u)
      have hH : Measurable H := by
        exact (measurable_fst.comp measurable_fst).mul
          (hg.comp ((measurable_snd.comp measurable_fst).prodMk
            measurable_snd))
      have hmeanState : Measurable (fun p : ℝ≥0∞ × ℝ =>
          p.1 * (∫⁻ ξ, g p.2 ξ ∂μ)) :=
        measurable_fst.mul (hmean.comp measurable_snd)
      have hpoint (p : ℝ≥0∞ × ℝ) :
          (∫⁻ ξ, H (p, ξ) ∂μ) =
            p.1 * (∫⁻ ξ, g p.2 ξ ∂μ) := by
        change (∫⁻ ξ, p.1 * g p.2 ξ ∂μ) = _
        rw [lintegral_const_mul]
        exact hg.comp (measurable_const.prodMk measurable_id)
      have hmarkLaw : (offspringFieldLaw μ).map mark = μ := by
        change (offspringFieldLaw μ).map (fun ω : StepField ℕ X => ω u) = μ
        exact offspringFieldLaw_coordinate μ u
      calc
        (∫⁻ ω, A u ω * g (position u ω) (ω u)
            ∂offspringFieldLaw μ) =
          ∫⁻ p, H p ∂(offspringFieldLaw μ).map pair := by
            exact (lintegral_map hH hpair).symm
        _ = ∫⁻ p, H p ∂(((offspringFieldLaw μ).map state).prod
              ((offspringFieldLaw μ).map mark)) := by
            rw [hind.map_prod_eq_prod_map_map hstate.aemeasurable
              (measurable_pi_apply u).aemeasurable]
        _ = ∫⁻ p, H p ∂(((offspringFieldLaw μ).map state).prod μ) := by
            rw [hmarkLaw]
        _ = ∫⁻ s, ∫⁻ ξ, H (s, ξ) ∂μ
              ∂(offspringFieldLaw μ).map state :=
            lintegral_prod H hH.aemeasurable
        _ = ∫⁻ s, s.1 * (∫⁻ ξ, g s.2 ξ ∂μ)
              ∂(offspringFieldLaw μ).map state := by
            apply lintegral_congr
            exact hpoint
        _ = ∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
              ∂offspringFieldLaw μ := by
            exact lintegral_map hmeanState hstate
    · have hzero : A u = fun _ => 0 := hsupport u hu
      simp [hzero]
  have hleft :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ) =
      ∑' u : TreeNode ℕ,
        ∫⁻ ω, A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (htermLeft u).aemeasurable
  have hright :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
        ∂offspringFieldLaw μ) =
      ∑' u : TreeNode ℕ,
        ∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
          ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (htermRight u).aemeasurable
  calc
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ) =
      ∑' u : TreeNode ℕ,
        ∫⁻ ω, A u ω * g (position u ω) (ω u) ∂offspringFieldLaw μ := hleft
    _ = ∑' u : TreeNode ℕ,
        ∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
          ∂offspringFieldLaw μ := by
        apply tsum_congr
        exact hfactor
    _ = ∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
        ∂offspringFieldLaw μ := hright.symm

end ProbabilityTheory.BranchingRandomWalk.Spine
