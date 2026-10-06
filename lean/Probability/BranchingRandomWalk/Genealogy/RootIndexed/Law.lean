/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Positions
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration
public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.StepField
public import Probability.BranchingRandomWalk.Step.Law
public import Combinatorics.BranchingWalk.Step.Monotone
public import Mathlib.Probability.Independence.InfinitePi
public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Product laws on root-indexed step fields

One i.i.d. step field is attached to each initial root through mathlib's
arbitrary-family probability product. The construction and its finite
marginals do not require a countable root type. Countability appears only when
coordinatewise almost-sure statements are combined over every root.
`finiteRoot...` is the `Fin m` marginal consumed by finite-population arguments.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

/-! ## The root-indexed product law -/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

noncomputable def RootIndexed.stepFieldLaw
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) :
    Measure (RootIndexed.StepField Root α X) :=
  Measure.infinitePi (fun _ : Root =>
    ProbabilityTheory.BranchingRandomWalk.stepFieldLaw (α := α) (X := X) μ)

instance RootIndexed.stepFieldLaw.isProbabilityMeasure
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  unfold RootIndexed.stepFieldLaw
  infer_instance

theorem RootIndexed.stepFieldLaw_reindex
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (f : NewRoot → Root) (hf : Function.Injective f) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.StepField.reindex f) =
      RootIndexed.stepFieldLaw (Root := NewRoot) μ := by
  unfold RootIndexed.stepFieldLaw
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Root =>
      ProbabilityTheory.BranchingRandomWalk.stepFieldLaw (α := α) (X := X) μ)
      (f := f) hf

/-- Mapping child marks commutes with the independent product over roots. -/
theorem RootIndexed.stepFieldLaw_mapMarks
    {Root α Mark Mark' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (f : Mark → Mark') (hf : Measurable f) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (fun field r => _root_.Combinatorics.Branching.StepField.map f
          (field r)) =
      RootIndexed.stepFieldLaw (Root := Root)
        (μ.map (Step.map f)) := by
  unfold RootIndexed.stepFieldLaw
  calc
    _ = Measure.infinitePi (fun _ : Root =>
        (_root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ).map
          (_root_.Combinatorics.Branching.StepField.map f)) := by
          exact Measure.infinitePi_map_pi
            (μ := fun _ : Root =>
              _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ)
            (f := fun (_ : Root)
                (field : _root_.Combinatorics.Branching.StepField α Mark) =>
              _root_.Combinatorics.Branching.StepField.map f field)
            (hf := fun (_ : Root) =>
              _root_.Combinatorics.Branching.StepField.map_measurable hf)
    _ = Measure.infinitePi (fun _ : Root =>
        _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
          (μ.map (Step.map f))) := by
          apply Measure.eq_infinitePi (μ := fun _ : Root =>
            _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
              (μ.map (Step.map f)))
          intro s t ht
          rw [Measure.infinitePi_pi _ (fun i _ => ht i)]
          apply Finset.prod_congr rfl
          intro r hr
          exact congrArg (fun ν : Measure
              (_root_.Combinatorics.Branching.StepField α Mark') => ν (t r))
            (ProbabilityTheory.BranchingRandomWalk.stepFieldLaw_mapMarks
              μ f hf).symm

/-- Coordinate reindexing is measurable for arbitrary root and slot types. -/
theorem RootIndexed.StepField.measurable_reindexCoordinates
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (f : NewRoot × TreeNode α → Root × TreeNode α) :
    Measurable (RootIndexed.StepField.reindexCoordinates
      (X := X) f) := by
  apply Measurable.of_eval
  intro r
  apply Measurable.of_eval
  intro u
  exact (measurable_pi_apply (f (r, u)).2).comp
    (measurable_pi_apply (f (r, u)).1)

/-- An injective relabelling of all root/address coordinates preserves the
i.i.d. root-indexed step-field law.  The map may mix source roots and
addresses; only freshness, expressed by injectivity, matters. -/
theorem RootIndexed.stepFieldLaw_reindexCoordinates
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (f : NewRoot × TreeNode α → Root × TreeNode α)
    (hf : Function.Injective f) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.StepField.reindexCoordinates f) =
      RootIndexed.stepFieldLaw (Root := NewRoot) μ := by
  let uncurryRoot :=
    (MeasurableEquiv.curry Root (TreeNode α) (Step α X)).symm
  let uncurryNewRoot :=
    (MeasurableEquiv.curry NewRoot (TreeNode α) (Step α X)).symm
  apply uncurryNewRoot.map_measurableEquiv_injective
  calc
    ((RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.StepField.reindexCoordinates f)).map uncurryNewRoot =
        (RootIndexed.stepFieldLaw (Root := Root) μ).map
          (fun ω p => ω (f p).1 (f p).2) := by
            rw [Measure.map_map]
            · rfl
            · exact uncurryNewRoot.measurable
            · exact RootIndexed.StepField.measurable_reindexCoordinates f
    _ = ((RootIndexed.stepFieldLaw (Root := Root) μ).map uncurryRoot).map
          (fun ω p => ω (f p)) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact uncurryRoot.measurable
    _ = (Measure.infinitePi
          (fun _ : Root × TreeNode α => μ)).map
          (fun ω p => ω (f p)) := by
            rw [show (RootIndexed.stepFieldLaw (Root := Root) μ).map
                uncurryRoot =
                Measure.infinitePi
                  (fun _ : Root × TreeNode α => μ) by
              simpa only [RootIndexed.stepFieldLaw,
                ProbabilityTheory.BranchingRandomWalk.stepFieldLaw,
                ProbabilityTheory.BranchingProcess.offspringFieldLaw,
                uncurryRoot] using
                (Measure.infinitePi_map_curry_symm
                  (μ := fun (_ : Root) (_ : TreeNode α) => μ))]
    _ = Measure.infinitePi
          (fun _ : NewRoot × TreeNode α => μ) := by
            simpa using
              (Measure.map_infinitePi_infinitePi_of_inj
                (P := fun _ : Root × TreeNode α => μ) hf)
    _ = (RootIndexed.stepFieldLaw (Root := NewRoot) μ).map
          uncurryNewRoot := by
            symm
            simpa only [RootIndexed.stepFieldLaw,
              ProbabilityTheory.BranchingRandomWalk.stepFieldLaw,
              ProbabilityTheory.BranchingProcess.offspringFieldLaw,
              uncurryNewRoot] using
              (Measure.infinitePi_map_curry_symm
                (μ := fun (_ : NewRoot) (_ : TreeNode α) => μ))

/-- Every labelled root/address coordinate is mutually independent under
the product law. The root and slot types remain arbitrary. -/
theorem RootIndexed.stepFieldLaw_coordinates_independent
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    iIndep (RootIndexed.stepCoordinateSpace (Root := Root) (α := α) (X := X))
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  have h : iIndepFun
      (fun (p : Root × TreeNode α)
        (ω : RootIndexed.StepField Root α X) => ω p.1 p.2)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
    unfold RootIndexed.stepFieldLaw _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      _root_.ProbabilityTheory.BranchingProcess.offspringFieldLaw
    simpa using (iIndepFun_uncurry_infinitePi'
      (μ := fun (_ : Root) (_ : TreeNode α) => μ)
      (X := fun (_ : Root) (_ : TreeNode α) => id)
      (fun _ _ => measurable_id))
  exact h.iIndep

/-- Every root has the same full pre-sampled step-field law. -/
theorem RootIndexed.stepFieldLaw_root_marginal
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (r : Root) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map (fun ω => ω r) =
      ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := α) (X := X) μ := by
  simpa [RootIndexed.stepFieldLaw] using
    (Measure.infinitePi_map_eval
      (fun _ : Root => ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
        (α := α) (X := X) μ) r)

/-- Every root/address coordinate has the original one-step law. -/
theorem RootIndexed.stepFieldLaw_coordinate_marginal
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (r : Root) (u : TreeNode α) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (fun ω => ω r u) = μ := by
  calc
    (RootIndexed.stepFieldLaw (Root := Root) μ).map (fun ω => ω r u) =
        ((RootIndexed.stepFieldLaw (Root := Root) μ).map
          (fun ω => ω r)).map (fun field => field u) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_pi_apply u
            · exact measurable_pi_apply r
    _ = μ := by
      rw [RootIndexed.stepFieldLaw_root_marginal
          (Root := Root) (α := α) μ r,
        stepFieldLaw_coordinate (α := α) μ u]

/-- The complete pre-sampled fields carried by distinct roots are mutually
independent. Consequently every finite injective family of root observations
is independent without constructing a separate finite-root probability
space. -/
theorem RootIndexed.stepFieldLaw_roots_independent
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    iIndepFun
      (fun r (ω : RootIndexed.StepField Root α X) => ω r)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  unfold RootIndexed.stepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Root => ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      (α := α) (X := X) μ)
    (X := fun _ => id) (fun _ => measurable_id))

/-- A one-step event of probability one holds simultaneously at every address
of every root in a countable root-indexed pre-sampled field. -/
theorem RootIndexed.stepFieldLaw_ae_all_of_measure_one
    {Root α X : Type*} [Countable Root] [Countable α] [MeasurableSpace X]
    {s : Set (Step α X)} (hs : MeasurableSet s)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (hμ : μ s = 1) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ r : Root, ∀ u : TreeNode α, field r u ∈ s := by
  apply ae_all_iff.2
  intro r
  apply ae_all_iff.2
  intro u
  have hmeas : Measurable
      (fun field : RootIndexed.StepField Root α X => field r u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply r)
  apply (ae_mem_iff_measure_eq (hmeas hs).nullMeasurableSet).2
  rw [← Measure.map_apply hmeas hs,
    RootIndexed.stepFieldLaw_coordinate_marginal
      (Root := Root) (α := α) μ r u,
    hμ]
  simp

/-! ## The finite-root case -/

noncomputable abbrev finiteRootStepFieldLaw
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) (m : ℕ) :
    Measure (FiniteRootStepField m α X) :=
  RootIndexed.stepFieldLaw (Root := Fin m) μ

/-- Any injectively labelled finite family is a finite marginal of the same
root-indexed pre-sampled probability space. -/
theorem RootIndexed.stepFieldLaw_fin_restrict
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {m : ℕ} (roots : Fin m → Root) (hroots : Function.Injective roots) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.StepField.reindex roots) =
      finiteRootStepFieldLaw μ m :=
  RootIndexed.stepFieldLaw_reindex μ roots hroots

theorem countableRootStepFieldLaw_first
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (m : ℕ) :
    (RootIndexed.stepFieldLaw (Root := ℕ) μ).map
        (RootIndexed.StepField.first m) =
      finiteRootStepFieldLaw μ m := by
  exact RootIndexed.stepFieldLaw_fin_restrict μ
    (fun i : Fin m => i.val) Fin.val_injective

theorem finiteRootStepFieldLaw_first
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {m n : ℕ} (h : m ≤ n) :
    (finiteRootStepFieldLaw μ n).map
        (FiniteRootStepField.first h) =
      finiteRootStepFieldLaw μ m := by
  exact RootIndexed.stepFieldLaw_reindex μ
    (Fin.castLE h) (fun a b hij =>
      Fin.ext (congrArg (fun z : Fin n => z.val) hij))

theorem finiteRootStepFieldLaw_root_marginal
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) :
    (finiteRootStepFieldLaw μ m).map (fun ω => ω i) =
      stepFieldLaw (α := α) μ := by
  exact RootIndexed.stepFieldLaw_root_marginal
    (Root := Fin m) (α := α) μ i

theorem finiteRootStepFieldLaw_coordinate_marginal
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) (u : TreeNode α) :
    (finiteRootStepFieldLaw μ m).map (fun ω => ω i u) = μ := by
  calc
    (finiteRootStepFieldLaw μ m).map (fun ω => ω i u) =
        ((finiteRootStepFieldLaw μ m).map (fun ω => ω i)).map
          (fun field => field u) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_pi_apply u
            · exact measurable_pi_apply i
    _ = μ := by rw [finiteRootStepFieldLaw_root_marginal μ i,
      stepFieldLaw_coordinate μ u]

theorem finiteRootStepFieldLaw_roots_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (m : ℕ) :
    iIndepFun (fun i (ω : FiniteRootStepField m α X) => ω i)
      (finiteRootStepFieldLaw μ m) := by
  exact RootIndexed.stepFieldLaw_roots_independent μ

/-- A one-node event of measure one transports to every coordinate of every
root of the finite-root product law. -/
theorem finiteRootStepFieldLaw_ae_all_of_measure_one
    {α X : Type*} [Countable α] [MeasurableSpace X]
    {s : Set (Step α X)} (hs : MeasurableSet s)
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (hμ : μ s = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : TreeNode α, step i u ∈ s :=
  RootIndexed.stepFieldLaw_ae_all_of_measure_one hs μ hμ

theorem finiteRootStepFieldLaw_all_ordered
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ orderedSteps = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ orderedSteps :=
  finiteRootStepFieldLaw_ae_all_of_measure_one
    orderedSteps_measurable μ hμ m

theorem finiteRootStepFieldLaw_all_nonempty
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ nonemptySupport = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, step i u ∈ nonemptySupport :=
  finiteRootStepFieldLaw_ae_all_of_measure_one
    nonemptySupport_measurable μ hμ m

/-- Ordered support together with the thesis's at-least-one-child assumption
forces slot zero at every address of every initial root, simultaneously. -/
theorem finiteRootStepFieldLaw_all_first_child
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hordered : μ orderedSteps = 1)
    (hnonempty : μ nonemptySupport = 1) (m : ℕ) :
    ∀ᵐ step ∂finiteRootStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, survive (step i u) 0 := by
  filter_upwards [finiteRootStepFieldLaw_all_ordered μ hordered m,
    finiteRootStepFieldLaw_all_nonempty μ hnonempty m] with step hord hne
  intro i u
  obtain ⟨j, hj⟩ := hne i u
  exact orderedSteps_survive_of_le (step i u) (hord i u) (Nat.zero_le j) hj

end ProbabilityTheory.BranchingRandomWalk
