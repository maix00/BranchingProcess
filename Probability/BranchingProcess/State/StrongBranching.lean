/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Descendants.Products
public import Probability.Process.Tree.Line.ConditionalExpectation

/-!
# Strong branching at arbitrary optional lines

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`, write `P_x = treeKernel K x`,
`T_u` for a complete descendant tree and `E_ℓ = {ω | ℓ ⊆ L(ω)}`.

* `condExp_prod_selectedDescendantTrees` proves
  `E[∏ᵢ gᵢ(T_(Rᵢ)) | F_L] = ∏ᵢ ∫ gᵢ dP_(X_(Rᵢ))` for a finite
  injective observed family `Rᵢ ∈ L` and strongly measurable real tests `|gᵢ| ≤ 1`.
* `setIntegral_prod_descendantTrees_optionalLine` proves the corresponding
  integral identity over `A ∩ E_ℓ` for each `A ∈ F_L` and deterministic finite cut `ℓ`.
* `condExp_prod_on_optionalLine` proves the full localized formula
  `E[1_(E_ℓ) ∏ᵢ gᵢ(T_(rᵢ)) | F_L] = 1_(E_ℓ) ∏ᵢ ∫ gᵢ dP_(X_(rᵢ))`.
  This includes lines of random size and samples where the line is empty.
* `descendantTreesKernel` constructs the native product kernel
  `κ(ω) = ⊗ᵢ P_(X_(Rᵢ(ω)))` on complete descendant trees, measurable in `F_L`.
* `descendantTreesKernel.isMarkovKernel` proves `κ(ω)(univ) = 1`.
* `hasCondDistrib_descendantTrees_optionalLine` identifies `κ` with the native
  `HasCondDistrib` of the entire observed family `(T_(Rᵢ))ᵢ` given `F_L`.
* `condExp_descendantTrees_optionalLine` proves `E[g((T_(Rᵢ))ᵢ) | F_L] = ∫ g dκ`
  for any strongly measurable Banach-valued test with integrable selected payoff.
* `condExp_selectedDescendantTree` derives the single-tree conditional identity
  `E[g(T_R) | F_L] = ∫ g dP_(X_R)` from that full-family theorem.

The offspring kernel is state-dependent and the initial roots have an arbitrary
joint law. State spaces are arbitrary measurable spaces. The optional line may
have unbounded depth, random cardinality and an uncountable range; membership need
not be decided from ancestors alone. The localized formula requires no enumeration
of `L`. An observed family used in the full-kernel interface needs countable range
for each chosen address, without a countability assumption on the family index.
No standard-Borel, coverage, order or moment assumption is imposed. Offspring
states in one parent's family need not be independent.

These are the conditional identities stated in P. Jagers and A. N. Lagerås,
*General branching processes conditioned on extinction are still branching
processes* (2008), §2.3, p. 543, DOI 10.1214/ECP.v13-1419, referring to
P. Jagers, *General branching processes as Markov fields* (1989), Theorem 4.14,
DOI 10.1016/0304-4149(89)90075-6. The model here is the existing discrete
state-dependent offspring-kernel tree. Continuous-time life histories require
their corresponding model and information interfaces.

The proof derives arbitrary deterministic-cut product identities from the actual
one-node outside-subtree law, localizes to optional cuts, and identifies the full
joint kernel law with native pi-system uniqueness. Generation and stopping-generation
specializations live in `State/Descendants/Observed.lean` and use this interface.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open MeasureTheory MeasurableSpace Combinatorics.UlamHarris Combinatorics.Branching

variable {Root α S : Type*} [MeasurableSpace S]

local notation "initialInformation" => MeasurableSpace.comap
  (rootStates (Root := Root) (α := α) (S := S)) inferInstance
local notation "reproductionInformation" =>
  fun u : RootIndexed.TreeNode Root α =>
    MeasurableSpace.comap (offspringStates (S := S) u) inferInstance

private lemma measurable_selected_descendantTree
    (choice : (Π n : ℕ, (Root × (Fin n → α)) → Option S) → RootIndexed.TreeNode Root α)
    (hcount : (Set.range choice).Countable)
    (hchoice : ∀ u, MeasurableSet {x | choice x = u}) :
    Measurable (fun x => descendantTree (choice x) x) := by
  classical
  let I := Set.range choice
  let c (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) : I := ⟨choice x, ⟨x, rfl⟩⟩
  let : Countable I := hcount.to_subtype
  let : MeasurableSpace I := ⊤
  let : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  have hcm : Measurable c := measurable_to_countable' (fun i => by
    have heq : c ⁻¹' {i} = {x | choice x = i.1} := by
      ext x
      exact Subtype.ext_iff
    rw [heq]
    exact hchoice i.1)
  have he : Measurable (fun p :
      (Π n : ℕ, (Root × (Fin n → α)) → Option S) × I => descendantTree p.2.1 p.1) :=
    measurable_from_prod_countable_left (fun i => descendantTree_measurable i.1)
  exact he.comp (measurable_id.prodMk hcm)

private lemma integrable_unit_product {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : I → Ω → ℝ)
    (hf : ∀ i, StronglyMeasurable (f i)) (hb : ∀ i x, ‖f i x‖ ≤ 1) :
    Integrable (fun x => ∏ i, f i x) μ := by
  apply Integrable.of_bound
    (Finset.univ.stronglyMeasurable_fun_prod (fun i _ => hf i)).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro x
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hb i x)

/-- Strong branching on an arbitrary optional line, expressed by all finite products
of bounded test functions at distinct observed boundary vertices.

This is the discrete offspring-kernel version of the optional-line identity in
P. Jagers and A. N. Lagerås, *General branching processes conditioned on extinction
are still branching processes* (2008), §2.3, p. 543, DOI 10.1214/ECP.v13-1419. -/
theorem condExp_prod_selectedDescendantTrees {J : Type*} [Fintype J]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (roots : (Π k : ℕ, (Root × (Fin k → α)) → Option S) → J →
      RootIndexed.TreeNode Root α)
    (hcount : ∀ i, (Set.range (fun x => roots x i)).Countable)
    (hroots : ∀ i u, MeasurableSet[h.measurableSpace] {x | roots x i = u})
    (hinj : ∀ x, Function.Injective (roots x)) (hmem : ∀ i x, roots x i ∈ L x)
    (g : J → (List α → Option S) → ℝ) (hg : ∀ i, StronglyMeasurable (g i))
    (hbound : ∀ i t, ‖g i t‖ ≤ 1) :
    (generationPathLaw K initial)[fun x => ∏ i, g i (descendantTree (roots x i) x) |
      h.measurableSpace] =ᵐ[generationPathLaw K initial]
      fun x => ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots x i) x) := by
  classical
  let I := Set.range roots
  have hrange : (Set.range roots).Countable :=
    (Set.countable_univ_pi hcount).mono (by
      rintro _ ⟨x, rfl⟩ i _
      exact ⟨x, rfl⟩)
  let : Countable I := hrange.to_subtype
  let c (x : Π k : ℕ, (Root × (Fin k → α)) → Option S) : I := ⟨roots x, ⟨x, rfl⟩⟩
  have hc (r : I) : MeasurableSet[h.measurableSpace] {x | c x = r} := by
    have heq : {x | c x = r} = ⋂ i : J, {x | roots x i = r.1 i} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Subtype.ext_iff, funext_iff, c]
    rw [heq]
    exact MeasurableSet.iInter (fun i => hroots i (r.1 i))
  have hrinj (r : I) : Function.Injective r.1 := by
    obtain ⟨x, hx⟩ := r.2
    rw [← hx]
    exact hinj x
  have hrline (r : I) : RootIndexed.IsLine (Set.range r.1) := by
    obtain ⟨x, hx⟩ := r.2
    rw [← hx]
    apply (h.isLine x).subset
    rintro _ ⟨i, rfl⟩
    exact hmem i x
  have hf (r : I) : Integrable (fun x => ∏ i, g i (descendantTree (r.1 i) x))
      (generationPathLaw K initial) :=
    integrable_unit_product (generationPathLaw K initial) _
      (fun i => (hg i).comp_measurable (descendantTree_measurable (r.1 i)))
      (fun i x => hbound i _)
  have hfi : Integrable (fun x => ∏ i, g i (descendantTree (roots x i) x))
      (generationPathLaw K initial) :=
    integrable_unit_product (generationPathLaw K initial) _
      (fun i => (hg i).comp_measurable (measurable_selected_descendantTree
        (fun x => roots x i) (hcount i) (fun u => h.measurableSpace_le _ (hroots i u))))
      (fun i x => hbound i _)
  have hm (i : J) : StronglyMeasurable[h.measurableSpace]
      (fun x => ∫ tree, g i tree ∂treeKernel K (stateAt (roots x i) x)) := by
    have hs := stateAt_measurable_selected h (fun x => roots x i)
      (hcount i) (hroots i) (hmem i)
    let : MeasurableSpace (Π k : ℕ, (Root × (Fin k → α)) → Option S) := h.measurableSpace
    exact (hg i).integral_kernel (κ := (treeKernel K).comap _ hs)
  have hmb (i : J) (x) :
      ‖∫ tree, g i tree ∂treeKernel K (stateAt (roots x i) x)‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := treeKernel K (stateAt (roots x i) x))
        (Filter.Eventually.of_forall (hbound i)))
  have hgm : StronglyMeasurable[h.measurableSpace]
      (fun x => ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots x i) x)) := by
    let : MeasurableSpace (Π k : ℕ, (Root × (Fin k → α)) → Option S) := h.measurableSpace
    exact Finset.univ.stronglyMeasurable_fun_prod (fun i _ => hm i)
  have hgi : Integrable (fun x => ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots x i) x))
      (generationPathLaw K initial) :=
    integrable_unit_product (generationPathLaw K initial) _
      (fun i => (hm i).mono h.measurableSpace_le) hmb
  exact h.condExp_of_selected_cut
    (fun _ _ hp => Tree.linePast_mono initialInformation reproductionInformation hp)
    (fun r : I => Set.range r.1) hrline (fun r => Set.countable_range r.1)
    (fun r => Tree.linePast_le initialInformation reproductionInformation
      rootStates_measurable.comap_le (fun v => (offspringStates_measurable v).comap_le) (Set.range r.1))
    (generationPathLaw K initial) c hc
    (fun x _ hx => by
      obtain ⟨i, rfl⟩ := hx
      exact hmem i x)
    (fun r x => ∏ i, g i (descendantTree (r.1 i) x))
    (fun r x => ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (r.1 i) x)) hf
    (fun r => condExp_prod_descendantTrees K initial r.1 (hrinj r) (hrline r) g hg hbound Finset.univ)
    hgm hfi hgi

/-- The strong branching identity localized to a deterministic finite cut.
It covers random lines of varying size, including samples where the line is empty. -/
theorem setIntegral_prod_descendantTrees_optionalLine {J : Type*} [Fintype J]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (roots : J → RootIndexed.TreeNode Root α) (hinj : Function.Injective roots)
    (hline : RootIndexed.IsLine (Set.range roots))
    (g : J → (List α → Option S) → ℝ) (hg : ∀ i, StronglyMeasurable (g i))
    (hbound : ∀ i t, ‖g i t‖ ≤ 1) {A : Set (Π n : ℕ, (Root × (Fin n → α)) → Option S)}
    (hA : MeasurableSet[h.measurableSpace] A) :
    ∫ x in A ∩ {x | Set.range roots ⊆ L x}, ∏ i, g i (descendantTree (roots i) x)
        ∂generationPathLaw K initial =
      ∫ x in A ∩ {x | Set.range roots ⊆ L x},
        ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x)
        ∂generationPathLaw K initial := by
  have hc := h.measurableSet_inter_subset
    (fun _ _ hp => Tree.linePast_mono initialInformation reproductionInformation hp)
    hline (Set.countable_range roots) hA
  have hle := Tree.linePast_le initialInformation reproductionInformation
    rootStates_measurable.comap_le (fun u => (offspringStates_measurable u).comap_le) (Set.range roots)
  have hf : Integrable (fun x => ∏ i, g i (descendantTree (roots i) x))
      (generationPathLaw K initial) := integrable_unit_product _ _
    (fun i => (hg i).comp_measurable (descendantTree_measurable (roots i)))
    (fun i x => hbound i _)
  have hd := condExp_prod_descendantTrees K initial roots hinj hline g hg hbound Finset.univ
  rw [← setIntegral_condExp hle hf hc]
  exact setIntegral_congr_ae (hle _ hc) (hd.mono fun _ hx _ => hx)

/-- Strong branching in a form valid for random cardinalities: on the observable
event that a deterministic finite cut lies on `L`, its complete descendant trees
have the conditional product moments prescribed by the boundary states. -/
theorem condExp_prod_on_optionalLine {J : Type*} [Fintype J]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (roots : J → RootIndexed.TreeNode Root α) (hinj : Function.Injective roots)
    (hline : RootIndexed.IsLine (Set.range roots))
    (g : J → (List α → Option S) → ℝ) (hg : ∀ i, StronglyMeasurable (g i))
    (hbound : ∀ i t, ‖g i t‖ ≤ 1) :
    (generationPathLaw K initial)[{x | Set.range roots ⊆ L x}.indicator
      (fun x => ∏ i, g i (descendantTree (roots i) x)) | h.measurableSpace]
      =ᵐ[generationPathLaw K initial] {x | Set.range roots ⊆ L x}.indicator
        (fun x => ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x)) := by
  classical
  let E := {x | Set.range roots ⊆ L x}
  have hE : MeasurableSet[h.measurableSpace] E := h.measurableSet_subset_stopped
    (fun _ _ hp => Tree.linePast_mono initialInformation reproductionInformation hp)
    (Set.range roots) (Set.countable_range roots)
  have hEm : MeasurableSet E := h.measurableSpace_le _ hE
  let q (i : J) (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
    if roots i ∈ L x then stateAt (roots i) x else none
  let m (i : J) (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) :=
    ∫ tree, g i tree ∂treeKernel K (q i x)
  have hq (i : J) : Measurable[h.measurableSpace] (q i) :=
    h.measurable_boundary_state initialInformation reproductionInformation
      rootStates_measurable.comap_le (fun u => (offspringStates_measurable u).comap_le)
      (roots i) (stateAt (roots i)) (stateAt_measurable_ancestralPast (roots i)) none
  have hm (i : J) : StronglyMeasurable[h.measurableSpace] (m i) := by
    let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) := h.measurableSpace
    exact (hg i).integral_kernel (κ := (treeKernel K).comap (q i) (hq i))
  have hmb (i : J) (x) : ‖m i x‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := treeKernel K (q i x))
        (Filter.Eventually.of_forall (hbound i)))
  have hgm : StronglyMeasurable[h.measurableSpace] (fun x => ∏ i, m i x) := by
    let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) := h.measurableSpace
    exact Finset.univ.stronglyMeasurable_fun_prod (fun i _ => hm i)
  have hgi : Integrable (fun x => ∏ i, m i x) (generationPathLaw K initial) :=
    integrable_unit_product _ _ (fun i => (hm i).mono h.measurableSpace_le) hmb
  have hfi : Integrable (fun x => ∏ i, g i (descendantTree (roots i) x))
      (generationPathLaw K initial) := integrable_unit_product _ _
    (fun i => (hg i).comp_measurable (descendantTree_measurable (roots i))) (fun i x => hbound i _)
  have heq (x) (hx : x ∈ E) : (∏ i, m i x) =
      ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x) := by
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [m, q]
    rw [ite_eq_left (hx (Set.mem_range_self i))]
  have hu : E.indicator (fun x => ∏ i, m i x) =ᵐ[generationPathLaw K initial]
      (generationPathLaw K initial)[E.indicator
        (fun x => ∏ i, g i (descendantTree (roots i) x)) | h.measurableSpace] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq h.measurableSpace_le (hfi.indicator hEm)
      (fun _ _ _ => (hgi.indicator hEm).integrableOn) _ (hgm.indicator hE).aestronglyMeasurable
    intro A hA _
    rw [setIntegral_indicator hEm, setIntegral_indicator hEm]
    calc
      _ = ∫ x in A ∩ E, ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x)
          ∂generationPathLaw K initial :=
        setIntegral_congr_fun (h.measurableSpace_le _ (hA.inter hE)) (fun x hx => heq x hx.2)
      _ = _ := (setIntegral_prod_descendantTrees_optionalLine K initial h roots hinj hline
        g hg hbound hA).symm
  refine hu.symm.trans (Filter.Eventually.of_forall fun x => ?_)
  change E.indicator (fun x => ∏ i, m i x) x =
    E.indicator (fun x => ∏ i, ∫ tree, g i tree ∂treeKernel K (stateAt (roots i) x)) x
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
    exact heq x hx
  · simp only [Set.indicator_of_notMem hx]

/-- Independent canonical continuations at observed boundary states. The law theorem
below identifies this native product kernel with the actual conditional tree law. -/
noncomputable def descendantTreesKernel {ι : Type*}
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (roots : ι → (Π n : ℕ, (Root × (Fin n → α)) → Option S) → RootIndexed.TreeNode Root α)
    (hcount : ∀ i, (Set.range (roots i)).Countable)
    (hroots : ∀ i u, MeasurableSet[h.measurableSpace] {x | roots i x = u})
    (hmem : ∀ i x, roots i x ∈ L x) :
    @Kernel (Π n : ℕ, (Root × (Fin n → α)) → Option S) (ι → List α → Option S)
      h.measurableSpace inferInstance := by
  have hs (i : ι) : Measurable[h.measurableSpace] (fun x => stateAt (roots i x) x) :=
    stateAt_measurable_selected h (roots i) (hcount i) (hroots i) (hmem i)
  let : MeasurableSpace (Π n : ℕ, (Root × (Fin n → α)) → Option S) := h.measurableSpace
  exact Kernel.infinitePi (fun i => (treeKernel K).comap (fun x => stateAt (roots i x) x) (hs i))

instance descendantTreesKernel.isMarkovKernel {ι : Type*}
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (roots : ι → (Π n : ℕ, (Root × (Fin n → α)) → Option S) → RootIndexed.TreeNode Root α)
    (hcount : ∀ i, (Set.range (roots i)).Countable)
    (hroots : ∀ i u, MeasurableSet[h.measurableSpace] {x | roots i x = u})
    (hmem : ∀ i x, roots i x ∈ L x) :
    @IsMarkovKernel _ _ h.measurableSpace inferInstance
      (descendantTreesKernel K h roots hcount hroots hmem) := by
  unfold descendantTreesKernel
  infer_instance

/-- The complete descendant-tree family at any optional line has the native
conditional law given by the product of the canonical inherited-state tree kernels.

This identifies the product law in P. Jagers and A. N. Lagerås, *General branching
processes conditioned on extinction are still branching processes* (2008), §2.3,
p. 543, DOI 10.1214/ECP.v13-1419, for the canonical discrete offspring-kernel model. -/
theorem hasCondDistrib_descendantTrees_optionalLine {ι : Type*}
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (roots : ι → (Π n : ℕ, (Root × (Fin n → α)) → Option S) → RootIndexed.TreeNode Root α)
    (hcount : ∀ i, (Set.range (roots i)).Countable)
    (hroots : ∀ i u, MeasurableSet[h.measurableSpace] {x | roots i x = u})
    (hinj : ∀ x, Function.Injective (fun i => roots i x))
    (hmem : ∀ i x, roots i x ∈ L x) :
    HasCondDistrib (m𝓧 := h.measurableSpace)
      (fun x i => descendantTree (roots i x) x) id
      (descendantTreesKernel K h roots hcount hroots hmem) (generationPathLaw K initial) := by
  classical
  let π (i : ι) : MeasurableSpace (ι → List α → Option S) :=
    MeasurableSpace.comap (Function.eval i) inferInstance
  let C := piiUnionInter (fun i => {B | MeasurableSet[π i] B}) Set.univ
  have hgen : (inferInstance : MeasurableSpace (ι → List α → Option S)) =
      MeasurableSpace.generateFrom C := by
    have hs : (⨆ i ∈ (Set.univ : Set ι), π i) =
        (inferInstance : MeasurableSpace (ι → List α → Option S)) := by
      simp only [Set.mem_univ, iSup_pos]
      rfl
    exact hs.symm.trans (generateFrom_piiUnionInter_measurableSet π Set.univ).symm
  have hpi : IsPiSystem C := isPiSystem_piiUnionInter _
    (fun i => @isPiSystem_measurableSet _ (π i)) Set.univ
  have hD : Measurable (fun x i => descendantTree (roots i x) x) :=
    measurable_pi_iff.mpr fun i => measurable_selected_descendantTree (roots i) (hcount i)
      (fun u => h.measurableSpace_le _ (hroots i u))
  refine @Kernel.hasCondDistrib_of_condExp_generator
    (Π n : ℕ, (Root × (Fin n → α)) → Option S)
    (Π n : ℕ, (Root × (Fin n → α)) → Option S) (ι → List α → Option S)
    inferInstance h.measurableSpace inferInstance (generationPathLaw K initial) inferInstance
    id (fun x i => descendantTree (roots i x) x)
    (measurable_id'' h.measurableSpace_le) hD
    (descendantTreesKernel K h roots hcount hroots hmem) inferInstance C hgen hpi ?_
  intro B hB
  obtain ⟨s, _, f, hf, rfl⟩ := hB
  have hex (i : ι) : ∃ A : Set (List α → Option S), MeasurableSet A ∧
      (i ∈ s → f i = Function.eval i ⁻¹' A) := by
    by_cases hi : i ∈ s
    · obtain ⟨A, hA, hEq⟩ := hf i hi
      exact ⟨A, hA, fun _ => hEq.symm⟩
    · exact ⟨Set.univ, MeasurableSet.univ, fun h => False.elim (hi h)⟩
  choose A hA hEq using hex
  have hset : (⋂ i ∈ s, f i) = Set.pi (s : Set ι) A := by
    ext y
    simp only [Set.mem_iInter, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro hy i hi
      have hm := hy i hi
      rwa [hEq i hi] at hm
    · intro hy i hi
      rw [hEq i hi]
      exact hy i hi
  rw [hset, MeasurableSpace.comap_id]
  have hp := condExp_prod_selectedDescendantTrees (J := s) K initial h
    (fun x i => roots i.1 x) (fun i => hcount i.1) (fun i => hroots i.1)
    (fun x => (hinj x).comp Subtype.val_injective) (fun i => hmem i.1)
    (fun i => (A i.1).indicator (fun _ => (1 : ℝ)))
    (fun i => stronglyMeasurable_const.indicator (hA i.1))
    (fun i t => by by_cases ht : t ∈ A i.1 <;> simp [ht])
  have hfun : (fun x => (Set.pi (s : Set ι) A).indicator (fun _ => (1 : ℝ))
      (fun i => descendantTree (roots i x) x)) =
      (fun x => ∏ i : s, (A i.1).indicator (fun _ => (1 : ℝ))
        (descendantTree (roots i.1 x) x)) := by
    funext x
    have hi := Set.indicator_pi_one_apply (M₀ := ℝ) s A
      (fun i => descendantTree (roots i x) x)
    exact hi.trans (Finset.prod_coe_sort s
      (fun i => (A i).indicator (1 : (List α → Option S) → ℝ)
        (descendantTree (roots i x) x))).symm
  rw [hfun]
  filter_upwards [hp] with x hx
  rw [hx]
  have hκ : (descendantTreesKernel K h roots hcount hroots hmem x).real (Set.pi (s : Set ι) A) =
      ∏ i ∈ s, (treeKernel K (stateAt (roots i x) x)).real (A i) := by
    change (Measure.infinitePi (fun i => treeKernel K (stateAt (roots i x) x))).real _ = _
    simp only [Measure.real, Measure.infinitePi_pi _ (fun i _ => hA i), ENNReal.toReal_prod]
  rw [id_eq, hκ]
  calc
    _ = ∏ i : s, (treeKernel K (stateAt (roots i.1 x) x)).real (A i.1) := by
      apply Finset.prod_congr rfl
      intro i _
      exact integral_indicator_one (hA i.1)
    _ = _ := Finset.prod_coe_sort s (fun i => (treeKernel K (stateAt (roots i x) x)).real (A i))

/-- Conditional integration of any integrable Banach-valued functional of the
complete family, derived from the native conditional-distribution identification. -/
theorem condExp_descendantTrees_optionalLine {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (roots : ι → (Π n : ℕ, (Root × (Fin n → α)) → Option S) → RootIndexed.TreeNode Root α)
    (hcount : ∀ i, (Set.range (roots i)).Countable)
    (hroots : ∀ i u, MeasurableSet[h.measurableSpace] {x | roots i x = u})
    (hinj : ∀ x, Function.Injective (fun i => roots i x)) (hmem : ∀ i x, roots i x ∈ L x)
    (g : (ι → List α → Option S) → E) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun x => g (fun i => descendantTree (roots i x) x))
      (generationPathLaw K initial)) :
    (generationPathLaw K initial)[fun x => g (fun i => descendantTree (roots i x) x) |
      h.measurableSpace] =ᵐ[generationPathLaw K initial]
      fun x => ∫ trees, g trees ∂descendantTreesKernel K h roots hcount hroots hmem x := by
  have hd := hasCondDistrib_descendantTrees_optionalLine K initial h roots hcount hroots hinj hmem
  have hD : Measurable (fun x i => descendantTree (roots i x) x) :=
    measurable_pi_iff.mpr fun i => measurable_selected_descendantTree (roots i) (hcount i)
      (fun u => h.measurableSpace_le _ (hroots i u))
  have hc := @Kernel.condExp_of_jointLaw
    (Π n : ℕ, (Root × (Fin n → α)) → Option S)
    (Π n : ℕ, (Root × (Fin n → α)) → Option S) (ι → List α → Option S) E
    inferInstance h.measurableSpace inferInstance inferInstance inferInstance inferInstance
    (generationPathLaw K initial) inferInstance id
    (fun x i => descendantTree (roots i x) x)
    (measurable_id'' h.measurableSpace_le) hD
    (descendantTreesKernel K h roots hcount hroots hmem) inferInstance hd.map_eq
    (fun p => g p.2) (hg.comp_measurable measurable_snd) hgi
  rw [MeasurableSpace.comap_id] at hc
  exact hc

/-- The complete subtree at an observed vertex of an arbitrary optional line
has the canonical law started at that vertex's inherited state. -/
theorem condExp_selectedDescendantTree {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    {L : (Π n : ℕ, (Root × (Fin n → α)) → Option S) →
      Set (RootIndexed.TreeNode Root α)}
    (h : Tree.IsOptionalLine (Tree.linePast initialInformation reproductionInformation) L)
    (choice : (Π n : ℕ, (Root × (Fin n → α)) → Option S) → RootIndexed.TreeNode Root α)
    (hcount : (Set.range choice).Countable)
    (hchoice : ∀ u, MeasurableSet[h.measurableSpace] {x | choice x = u})
    (hmem : ∀ x, choice x ∈ L x)
    (g : (List α → Option S) → E) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun x => g (descendantTree (choice x) x))
      (generationPathLaw K initial)) :
    (generationPathLaw K initial)[fun x => g (descendantTree (choice x) x) |
      h.measurableSpace] =ᵐ[generationPathLaw K initial]
      fun x => ∫ tree, g tree ∂treeKernel K (stateAt (choice x) x) := by
  have hc := condExp_descendantTrees_optionalLine K initial h (fun _ : Unit => choice)
    (fun _ => hcount) (fun _ => hchoice)
    (fun x i j _ => Subsingleton.elim i j) (fun _ => hmem)
    (fun t => g (t ())) (hg.comp_measurable (measurable_pi_apply ())) hgi
  filter_upwards [hc] with x hx
  refine hx.trans ?_
  change (∫ t : Unit → List α → Option S, g (t ()) ∂Measure.infinitePi
      (fun _ : Unit => treeKernel K (stateAt (choice x) x))) =
    ∫ tree, g tree ∂treeKernel K (stateAt (choice x) x)
  have hi := integral_map (μ := Measure.infinitePi
    (fun _ : Unit => treeKernel K (stateAt (choice x) x)))
    (φ := fun t => t ()) (measurable_pi_apply ()).aemeasurable hg.aestronglyMeasurable
  rw [Measure.infinitePi_map_eval] at hi
  exact hi.symm

end ProbabilityTheory.BranchingProcess.State

end
