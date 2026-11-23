/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Descendants.SingleNode
public import MeasureTheory.Function.ConditionalExpectation.FiniteProduct

/-!
# Ordinary branching on arbitrary deterministic lines

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `condExp_prod_descendantTrees` proves
  `E[∏_(i ∈ s) gᵢ(T_(rᵢ)) | F_(range r)] = ∏_(i ∈ s) ∫ gᵢ dP_(X_(rᵢ))`
  for every finite index set `s`, when `r` injectively indexes any deterministic
  ancestry line and the real test functions are strongly measurable with
  `|gᵢ| ≤ 1`.

The indexed cut may have different depths, infinitely many nodes, and no depth
bound. No countability, standard-Borel, order or moment hypothesis is imposed.
This finite-product identity expresses conditional independence and the canonical
marginal laws on that cut, without requiring regular conditional distributions.
It uses the actual generation-path law with arbitrary joint initial root states.

This is the deterministic-line product formula in P. Jagers and A. N. Lagerås,
*General branching processes conditioned on extinction are still branching
processes* (2008), §2.3, p. 543, DOI 10.1214/ECP.v13-1419. Each coordinate is
conditioned on its full outside-subtree information; the abstract conditional
finite-product theorem combines these identities by the native tower and
pull-out properties.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open MeasureTheory Combinatorics.UlamHarris Combinatorics.Branching

variable {Root α S : Type*} [MeasurableSpace S]

local notation "initialInformation" => MeasurableSpace.comap
  (rootStates (Root := Root) (α := α) (S := S)) inferInstance
local notation "reproductionInformation" =>
  fun u : RootIndexed.TreeNode Root α =>
    MeasurableSpace.comap (offspringStates (S := S) u) inferInstance

private lemma norm_prod_le_one {I Ω : Type*} (f : I → Ω → ℝ)
    (hb : ∀ i x, ‖f i x‖ ≤ 1) (s : Finset I) (x : Ω) : ‖(∏ i ∈ s, f i) x‖ ≤ 1 := by
  rw [Finset.prod_apply, norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hb i x)

/-- The complete descendant trees on an arbitrary deterministic line are
conditionally independent, with the laws prescribed by their inherited states.

The deterministic-line identity is stated by P. Jagers and A. N. Lagerås,
*General branching processes conditioned on extinction are still branching processes*
(2008), §2.3, p. 543, DOI 10.1214/ECP.v13-1419. -/
theorem condExp_prod_descendantTrees {I : Type*}
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    (roots : I → RootIndexed.TreeNode Root α) (hinj : Function.Injective roots)
    (hline : RootIndexed.IsLine (Set.range roots))
    (g : I → (List α → Option S) → ℝ) (hg : ∀ i, StronglyMeasurable (g i))
    (hbound : ∀ i t, ‖g i t‖ ≤ 1) (s : Finset I) :
    (generationPathLaw K initial)[fun x => ∏ i ∈ s, g i (descendantTree (roots i) x) |
      Tree.linePast initialInformation reproductionInformation (Set.range roots)]
      =ᵐ[generationPathLaw K initial]
      fun x => ∏ i ∈ s, ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x) := by
  classical
  let f (i : I) (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
    g i (descendantTree (roots i) x)
  let m (i : I) (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
    ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x)
  have hf (i : I) : StronglyMeasurable (f i) :=
    (hg i).comp_measurable (descendantTree_measurable (roots i))
  have hfb (i : I) (x) : ‖f i x‖ ≤ 1 := hbound i _
  have hm : ∀ i, StronglyMeasurable[
      Tree.linePast initialInformation reproductionInformation (Set.range roots)] (m i) := by
    intro i
    have hinfo := Tree.ancestralPast_le_linePast initialInformation reproductionInformation
      hline (Set.mem_range_self i) (RootIndexed.IsAncestor.refl (roots i))
    have hs := (stateAt_measurable_ancestralPast (S := S) (roots i)).mono hinfo le_rfl
    let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
      Tree.linePast initialInformation reproductionInformation (Set.range roots)
    exact (hg i).integral_kernel (κ := (treeKernel K).comap _ hs)
  have hmb (i : I) (x) : ‖m i x‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := treeKernel K (stateAt (roots i) x))
        (Filter.Eventually.of_forall (hbound i)))
  have hle := Tree.linePast_le initialInformation reproductionInformation
    rootStates_measurable.comap_le (fun u => (offspringStates_measurable u).comap_le)
  have hfi (t : Finset I) : Integrable (∏ i ∈ t, f i) (generationPathLaw K initial) :=
    Integrable.of_bound (t.stronglyMeasurable_prod (fun i _ => hf i)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (norm_prod_le_one f hfb t))
  have hmix (i : I) (t : Finset I) :
      Integrable (m i * ∏ j ∈ t, f j) (generationPathLaw K initial) := by
    apply Integrable.of_bound
      (((hm i).mono (hle (Set.range roots))).mul
        (t.stronglyMeasurable_prod (fun j _ => hf j))).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro x
    calc
      ‖(m i * ∏ j ∈ t, f j) x‖ = ‖m i x‖ * ‖(∏ j ∈ t, f j) x‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hmb i x) (norm_prod_le_one f hfb t x) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hcross (i j : I) (hij : i ≠ j) :
      StronglyMeasurable[Tree.linePast initialInformation reproductionInformation {roots i}]
        (f j) := by
    have hne : roots j ∉ ({roots i} : Set (RootIndexed.TreeNode Root α)) := by
      intro heq
      exact hij (hinj (Set.mem_singleton_iff.mp heq)).symm
    have hp : RootIndexed.IsLine (insert (roots j) {roots i}) := by
      apply hline.subset
      intro u hu
      rcases hu with hu | hu
      · exact hu ▸ Set.mem_range_self j
      · exact (Set.mem_singleton_iff.mp hu) ▸ Set.mem_range_self i
    exact (hg j).comp_measurable (descendantTree_measurable_linePast (roots j) {roots i} hp hne)
  have h := condExp_finsetProd_of_complement (hle (Set.range roots))
    (fun i => Tree.linePast initialInformation reproductionInformation {roots i})
    (fun i => hle {roots i})
    (fun i => Tree.linePast_mono initialInformation reproductionInformation
      (fun v hv => by
        have heq : v = roots i := Set.mem_singleton_iff.mp hv
        subst v
        exact ⟨roots i, Set.mem_range_self i, RootIndexed.IsAncestor.refl _⟩))
    (generationPathLaw K initial) f m hm hcross
    (fun i => condExp_descendantTree K initial (roots i) (g i) (hg i)
      (by simpa only [Finset.prod_singleton] using hfi {i})) hfi hmix s
  have hfp : (∏ i ∈ s, f i) =
      (fun x => ∏ i ∈ s, g i (descendantTree (roots i) x)) := by
    funext x
    simp only [Finset.prod_apply, f]
  have hmp : (∏ i ∈ s, m i) =
      (fun x => ∏ i ∈ s, ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x)) := by
    funext x
    simp only [Finset.prod_apply, m]
  rw [hfp, hmp] at h
  exact h

end ProbabilityTheory.BranchingProcess.State

end
