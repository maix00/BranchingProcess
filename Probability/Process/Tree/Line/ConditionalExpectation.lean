/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Tree.Line.Information.Localization
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional identities at nodes selected from an optional line

## Public declarations

In `ProbabilityTheory.Tree`:

* `IsOptionalLine.condExp_of_selected_cut`: let `c` be an `F_L`-measurable
  choice from countably many deterministic countable cuts `ℓᵢ`, with
  `ℓ_(c(ω)) ⊆ L(ω)`. If `E[fᵢ | F_(ℓᵢ)] = gᵢ`, then
  `E[f_(c(ω))(ω) | F_L] = g_(c(ω))(ω)`, provided the selected right-hand
  side is `F_L`-strongly measurable and both selected payoffs are integrable.
  The deterministic payoffs must also be integrable.

The optional line itself may have unbounded depth and an uncountable range.
Only the family of tested cuts is countable: for countable node addresses this
includes every finite tuple of selected incomparable nodes. The integrability
and stopped measurability assumptions on the selected payoff are explicit;
they do not follow just from the deterministic conditional identities.

This is an information-theoretic transfer theorem, without a branching-law
assumption. To obtain strong branching one must separately prove the ordinary
branching conditional identities for arbitrary deterministic cuts, instantiate
`gᵢ` with the product-tree kernel integrals, and prove stopped measurability
of those boundary-state integrals. Fixed-generation branching alone is not that
premise. The intended branching identity is stated in P. Jagers and
A. N. Lagerås, *General branching processes conditioned on extinction are still
branching processes* (2008), §2.3, p. 543, DOI 10.1214/ECP.v13-1419;
see P. Jagers, *General branching processes as Markov fields* (1989),
Theorem 4.14, DOI 10.1016/0304-4149(89)90075-6.

The proof reuses native conditional-expectation uniqueness, set integrals, and
countable disjoint-union integration. There is no parallel definition of
conditional expectation or conditional independence.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open Classical MeasureTheory Combinatorics.UlamHarris

/-- Transfer deterministic-cut conditional identities to an observed choice of
nodes on an arbitrary optional line. The selected conditional integral must be
measurable in the stopped information, as is required for any conditional law. -/
theorem IsOptionalLine.condExp_of_selected_cut
    {Ω Root α I E : Type*} [mΩ : MeasurableSpace Ω] [Countable I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {past : Set (RootIndexed.TreeNode Root α) → MeasurableSpace Ω}
    {L : Ω → Set (RootIndexed.TreeNode Root α)}
    (h : IsOptionalLine past L)
    (hmono : ∀ {a b}, RootIndexed.IsLine a → RootIndexed.IsLine b →
      RootIndexed.Line.Precedes a b → past a ≤ past b)
    (cuts : I → Set (RootIndexed.TreeNode Root α))
    (hcuts : ∀ i, RootIndexed.IsLine (cuts i))
    (hcount : ∀ i, (cuts i).Countable) (hpast : ∀ i, past (cuts i) ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (choice : Ω → I) (hchoice : ∀ i, MeasurableSet[h.measurableSpace] {ω | choice ω = i})
    (hsubset : ∀ ω, cuts (choice ω) ⊆ L ω)
    (f g : I → Ω → E) (hf : ∀ i, Integrable (f i) μ)
    (hdet : ∀ i, μ[f i | past (cuts i)] =ᵐ[μ] g i)
    (hselected : StronglyMeasurable[h.measurableSpace] (fun ω => g (choice ω) ω))
    (hfi : Integrable (fun ω => f (choice ω) ω) μ)
    (hgi : Integrable (fun ω => g (choice ω) ω) μ) :
    μ[fun ω => f (choice ω) ω | h.measurableSpace] =ᵐ[μ]
      fun ω => g (choice ω) ω := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq h.measurableSpace_le hfi
    (fun _ _ _ => hgi.integrableOn) ?_ hselected.aestronglyMeasurable).symm
  intro A hA _
  let B (i : I) := A ∩ {ω | choice ω = i}
  have hBstop (i : I) : MeasurableSet[h.measurableSpace] (B i) :=
    hA.inter (hchoice i)
  have hB (i : I) : MeasurableSet (B i) := h.measurableSpace_le _ (hBstop i)
  have hBpast (i : I) : MeasurableSet[past (cuts i)] (B i) := by
    have hm := h.measurableSet_inter_subset hmono (hcuts i) (hcount i) (hBstop i)
    have heq : B i ∩ {ω | cuts i ⊆ L ω} = B i := by
      apply Set.inter_eq_left.mpr
      intro ω hω
      exact (hω.2 ▸ hsubset ω)
    rwa [heq] at hm
  have hdisj : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hcover : (⋃ i, B i) = A := by
    ext ω
    simp only [Set.mem_iUnion, B, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, hω, _⟩
      exact hω
    · intro hω
      exact ⟨choice ω, hω, rfl⟩
  have hcell (i : I) :
      ∫ ω in B i, g (choice ω) ω ∂μ = ∫ ω in B i, f (choice ω) ω ∂μ := by
    calc
      _ = ∫ ω in B i, g i ω ∂μ :=
        setIntegral_congr_fun (hB i) (fun ω hω => by rw [hω.2])
      _ = ∫ ω in B i, (μ[f i | past (cuts i)]) ω ∂μ :=
        (setIntegral_congr_ae (hB i) ((hdet i).mono fun _ hx _ => hx)).symm
      _ = ∫ ω in B i, f i ω ∂μ := setIntegral_condExp (hpast i) (hf i) (hBpast i)
      _ = _ := setIntegral_congr_fun (hB i) (fun ω hω => by rw [hω.2])
  calc
    _ = ∑' i, ∫ ω in B i, g (choice ω) ω ∂μ := by
      rw [← hcover]
      exact integral_iUnion hB hdisj hgi.integrableOn
    _ = ∑' i, ∫ ω in B i, f (choice ω) ω ∂μ := tsum_congr hcell
    _ = _ := by
      rw [← hcover]
      exact (integral_iUnion hB hdisj hfi.integrableOn).symm

end ProbabilityTheory.Tree

end
