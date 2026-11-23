/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.StrongBranching
public import Mathlib.Probability.Process.Stopping

/-!
# Branching at nodes chosen from the observed history

## Public declarations

* `ProbabilityTheory.BranchingProcess.State.condExp_descendantTrees`:
  for deterministic distinct depth-`a` nodes,
  `E[g((Tᵢ)ᵢ) | Fₐ] = ∫ g d(⊗ᵢ P_(Xₐ(rᵢ)))`, derived from optional-line
  branching without countability assumptions on the node spaces.
* `ProbabilityTheory.BranchingProcess.State.condExp_selectedDescendantTrees`:
  for distinct depth-$a$ addresses $R_i$ measurable in the generation history,
  $E[g((T_{R_i})_i)\mid\mathcal F_a]
    =\int g\,d\bigotimes_i P_{X_a(R_i)}$.
* `ProbabilityTheory.BranchingProcess.State.stopped_descendantTrees_condExp`
  derives the same formula from the optional-line theorem on the finite-time
  event of any stopping time,
  with nodes selected
  from its observed history. Each fixed-time and stopped payoff is integrable.

  The initial root states may have any joint distribution, and the offspring
  law may depend on the parent state.

The history-selected address interfaces assume countable root and child spaces
with measurable singletons; deterministic nodes need no such assumptions.
The state space is arbitrary measurable. All three formulas specialize the
optional-line law, with native stopping-time localization for the last one.
Conditional independence is derived from the constructed path law; it is not an assumption on the selected descendants.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

private lemma generationLine_information {Root α S : Type*} [MeasurableSpace S] (a : ℕ) :
    (Tree.IsOptionalLine.const (Tree.linePast
      (MeasurableSpace.comap (rootStates (Root := Root) (α := α) (S := S)) inferInstance)
      (fun u => MeasurableSpace.comap (offspringStates (S := S) u) inferInstance))
      (RootIndexed.isLine_generation a)).measurableSpace =
    Filtration.piLE (X := fun k : ℕ => (Root × (Fin k → α)) → Option S) a := by
  exact (Tree.IsOptionalLine.measurableSpace_const
    (fun _ _ hp => Tree.linePast_mono _ _ hp) (RootIndexed.isLine_generation a)
    (Tree.linePast_le _ _ rootStates_measurable.comap_le
      (fun u => (offspringStates_measurable u).comap_le) {u | u.2.length = a})).trans
    (linePast_generation_eq_piLE a)

/-- The general branching identity remains valid for distinct nodes selected
measurably from the current history. -/
theorem condExp_selectedDescendantTrees {Root ι α S E : Type*}
    [MeasurableSpace Root] [MeasurableSpace α] [MeasurableSpace S]
    [Countable Root] [Countable α]
    [MeasurableSingletonClass Root] [MeasurableSingletonClass α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    (a : ℕ)
    (roots : (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) →
      ι → Root × (Fin a → α))
    (hroots : ∀ i, Measurable (fun h ↦ roots h i))
    (hinj : ∀ h, Function.Injective (roots h))
    (g : (ι → List α → Option S) → E) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦
      g (fun i (u : List α) ↦ x (a + u.length)
        ((roots (frestrictLe a x) i).1, Fin.append (roots (frestrictLe a x) i).2 u.get)))
      (generationPathLaw K initial)) :
    (generationPathLaw K initial)[fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦
      g (fun i (u : List α) ↦ x (a + u.length)
        ((roots (frestrictLe a x) i).1, Fin.append (roots (frestrictLe a x) i).2 u.get)) |
      Filtration.piLE (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S) a]
      =ᵐ[generationPathLaw K initial]
        fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦
          ∫ trees, g trees ∂Measure.infinitePi
            (fun i : ι ↦ treeKernel K (x a (roots (frestrictLe a x) i))) := by
  let line := {u : RootIndexed.TreeNode Root α | u.2.length = a}
  have hline : RootIndexed.IsLine line := RootIndexed.isLine_generation a
  let hL := Tree.IsOptionalLine.const (Tree.linePast
    (MeasurableSpace.comap (rootStates (Root := Root) (α := α) (S := S)) inferInstance)
    (fun u => MeasurableSpace.comap (offspringStates (S := S) u) inferInstance)) hline
  have hi : hL.measurableSpace =
      Filtration.piLE (X := fun k : ℕ => (Root × (Fin k → α)) → Option S) a :=
    generationLine_information (Root := Root) (α := α) (S := S) a
  let R (i : ι) (x : Π k : ℕ, (Root × (Fin k → α)) → Option S) :
      RootIndexed.TreeNode Root α :=
    ((roots (frestrictLe a x) i).1, List.ofFn (roots (frestrictLe a x) i).2)
  have hR (i : ι) : @Measurable _ (RootIndexed.TreeNode Root α)
      (Filtration.piLE (X := fun k : ℕ => (Root × (Fin k → α)) → Option S) a) ⊤ (R i) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    let : MeasurableSpace (RootIndexed.TreeNode Root α) := ⊤
    have hh : Measurable[MeasurableSpace.comap (frestrictLe a) inferInstance]
        (frestrictLe a : (Π k : ℕ, (Root × (Fin k → α)) → Option S) → _) :=
      Measurable.of_comap_le le_rfl
    exact (measurable_of_countable
      (fun p : Root × (Fin a → α) => (p.1, List.ofFn p.2))).comp ((hroots i).comp hh)
  have hRf (i : ι) (u : RootIndexed.TreeNode Root α) :
      MeasurableSet[hL.measurableSpace] {x | R i x = u} := by
    rw [hi]
    exact (hR i) (show @MeasurableSet (RootIndexed.TreeNode Root α) ⊤ {u} from trivial)
  have hRi (x) : Function.Injective (fun i => R i x) := by
    intro i j heq
    apply hinj (frestrictLe a x)
    apply Prod.ext
    · exact congrArg (fun p : RootIndexed.TreeNode Root α => p.1) heq
    · exact List.ofFn_injective (congrArg (fun p : RootIndexed.TreeNode Root α => p.2) heq)
  have hRm (i : ι) (x) : R i x ∈ line := by simp [line, R]
  have hD (x : Π k : ℕ, (Root × (Fin k → α)) → Option S) :
      (fun i => descendantTree (R i x) x) = fun i (u : List α) =>
        x (a + u.length) ((roots (frestrictLe a x) i).1,
          Fin.append (roots (frestrictLe a x) i).2 u.get) := by
    funext i u
    exact descendantTree_ofFn x a (roots (frestrictLe a x) i) u
  have hc := condExp_descendantTrees_optionalLine K initial hL R
    (fun _ => Set.to_countable _) hRf hRi hRm g hg (by simpa only [hD] using hgi)
  have hp : (fun x => g (fun i => descendantTree (R i x) x)) =
      (fun x => g (fun i (u : List α) => x (a + u.length)
        ((roots (frestrictLe a x) i).1, Fin.append (roots (frestrictLe a x) i).2 u.get))) :=
    funext fun x => congrArg g (hD x)
  have hCE : (generationPathLaw K initial)[fun x => g (fun i => descendantTree (R i x) x) |
      hL.measurableSpace] = (generationPathLaw K initial)[
        fun x => g (fun i => descendantTree (R i x) x) | Filtration.piLE a] :=
    congrArg (fun m => (generationPathLaw K initial)[
      fun x => g (fun i => descendantTree (R i x) x) | m]) hi
  rw [hCE, hp] at hc
  filter_upwards [hc] with x hx
  refine hx.trans ?_
  apply congrArg (fun μ => ∫ trees, g trees ∂μ)
  change Measure.infinitePi (fun i => treeKernel K (stateAt (R i x) x)) = _
  congr 1
  funext i
  rw [show stateAt (R i x) x = x a (roots (frestrictLe a x) i) from
    stateAt_ofFn x a (roots (frestrictLe a x) i)]

/-- The state-dependent branching identity under an arbitrary joint initial law. -/
theorem condExp_descendantTrees {Root ι α S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    (a : ℕ) (roots : ι → Root × (Fin a → α)) (hinj : Function.Injective roots)
    (g : (ι → List α → Option S) → E) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦ g (fun i (u : List α) ↦
      x (a + u.length) ((roots i).1, Fin.append (roots i).2 u.get)))
      (generationPathLaw (Root := Root) K initial)) :
    (generationPathLaw (Root := Root) K initial)[
      fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦ g (fun i (u : List α) ↦
        x (a + u.length) ((roots i).1, Fin.append (roots i).2 u.get)) |
        Filtration.piLE (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S) a]
      =ᵐ[generationPathLaw (Root := Root) K initial]
      fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦ ∫ trees, g trees ∂Measure.infinitePi
        (fun i : ι ↦ treeKernel K (x a (roots i))) := by
  let line := {u : RootIndexed.TreeNode Root α | u.2.length = a}
  let hL := Tree.IsOptionalLine.const (Tree.linePast
    (MeasurableSpace.comap (rootStates (Root := Root) (α := α) (S := S)) inferInstance)
    (fun u => MeasurableSpace.comap (offspringStates (S := S) u) inferInstance))
    (RootIndexed.isLine_generation a)
  have hi : hL.measurableSpace =
      Filtration.piLE (X := fun k : ℕ => (Root × (Fin k → α)) → Option S) a :=
    generationLine_information (Root := Root) (α := α) (S := S) a
  let R (i : ι) (_x : Π k : ℕ, (Root × (Fin k → α)) → Option S) :
      RootIndexed.TreeNode Root α := ((roots i).1, List.ofFn (roots i).2)
  have hcount (i : ι) : (Set.range (R i)).Countable :=
    (Set.countable_singleton ((roots i).1, List.ofFn (roots i).2)).mono (by
      rintro _ ⟨x, rfl⟩
      exact Set.mem_singleton _)
  have hRf (i : ι) (u : RootIndexed.TreeNode Root α) :
      MeasurableSet[hL.measurableSpace] {x | R i x = u} :=
    @MeasurableSet.const _ hL.measurableSpace (((roots i).1, List.ofFn (roots i).2) = u)
  have hRi (x) : Function.Injective (fun i => R i x) := by
    intro i j heq
    apply hinj
    apply Prod.ext
    · exact congrArg (fun p : RootIndexed.TreeNode Root α => p.1) heq
    · exact List.ofFn_injective (congrArg (fun p : RootIndexed.TreeNode Root α => p.2) heq)
  have hRm (i : ι) (x) : R i x ∈ line := by simp [line, R]
  have hD (x : Π k : ℕ, (Root × (Fin k → α)) → Option S) :
      (fun i => descendantTree (R i x) x) = fun i (u : List α) =>
        x (a + u.length) ((roots i).1, Fin.append (roots i).2 u.get) := by
    funext i u
    exact descendantTree_ofFn x a (roots i) u
  have hc := condExp_descendantTrees_optionalLine K initial hL R hcount hRf hRi hRm g hg
    (by simpa only [hD] using hgi)
  have hCE : (generationPathLaw K initial)[fun x => g (fun i => descendantTree (R i x) x) |
      hL.measurableSpace] = (generationPathLaw K initial)[
        fun x => g (fun i => descendantTree (R i x) x) | Filtration.piLE a] :=
    congrArg (fun m => (generationPathLaw K initial)[
      fun x => g (fun i => descendantTree (R i x) x) | m]) hi
  have hp : (fun x => g (fun i => descendantTree (R i x) x)) =
      (fun x => g (fun i (u : List α) => x (a + u.length)
        ((roots i).1, Fin.append (roots i).2 u.get))) :=
    funext fun x => congrArg g (hD x)
  rw [hCE, hp] at hc
  filter_upwards [hc] with x hx
  refine hx.trans ?_
  apply congrArg (fun μ => ∫ trees, g trees ∂μ)
  change Measure.infinitePi (fun i => treeKernel K (stateAt (R i x) x)) = _
  congr 1
  funext i
  rw [show stateAt (R i x) x = x a (roots i) from stateAt_ofFn x a (roots i)]

/-- State-dependent branching on the finite-time event of a stopping generation, including
nodes chosen from the observed history. The proof specializes the optional-line
identity to generations and uses native stopping-time localization on each event $\{\tau=n\}$. -/
theorem stopped_descendantTrees_condExp {Root ι α S : Type*}
    [MeasurableSpace Root] [MeasurableSpace α] [MeasurableSpace S]
    [Countable Root] [Countable α]
    [MeasurableSingletonClass Root] [MeasurableSingletonClass α]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    (τ : (Π n : ℕ, (Root × (Fin n → α)) → Option S) → WithTop ℕ)
    (hτ : IsStoppingTime Filtration.piLE τ)
    (roots : (a : ℕ) → (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) →
      ι → Root × (Fin a → α))
    (hroots : ∀ a i, Measurable (fun h ↦ roots a h i))
    (hinj : ∀ a h, Function.Injective (roots a h))
    (g : (ι → List α → Option S) → ℝ) (hg : StronglyMeasurable g) :
    let D := fun a (p : (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) ×
        (Π n : ℕ, (Root × (Fin n → α)) → Option S)) i (u : List α) ↦
      p.2 (a + u.length) ((roots a p.1 i).1, Fin.append (roots a p.1 i).2 u.get)
    (∀ a, Integrable (fun x ↦ g (D a (frestrictLe a x, x)))
      (generationPathLaw K initial)) →
    Integrable (fun x ↦ g (D ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, x)))
      (generationPathLaw K initial) →
    (generationPathLaw K initial)[fun x ↦ g (D ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, x)) |
      hτ.measurableSpace] =ᵐ[(generationPathLaw K initial).restrict {x | τ x ≠ ⊤}]
      fun x ↦ ∫ trees, g trees ∂Measure.infinitePi
        (fun i : ι ↦ treeKernel K (x ((τ x).untopD 0)
          (roots ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x) i))) := by
  intro D hgi hstop
  let P := generationPathLaw K initial
  let f := fun x => g (D ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, x))
  have hall : P[f | hτ.measurableSpace] =ᵐ[P.restrict (⋃ n : ℕ, {x | τ x = n})]
      fun x => ∫ trees, g trees ∂Measure.infinitePi
        (fun i : ι => treeKernel K (x ((τ x).untopD 0)
          (roots ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x) i))) := by
    rw [ae_eq_restrict_iUnion_iff]
    intro n
    let A := {x | τ x = n}
    have hA : MeasurableSet[Filtration.piLE n] A := hτ.measurableSet_eq n
    have hAm : MeasurableSet A := Filtration.piLE.le n _ hA
    have hdiff : (fun x => f x - g (D n (frestrictLe n x, x))) =ᵐ[P.restrict A] 0 := by
      filter_upwards [ae_restrict_mem hAm] with x hx
      change τ x = (n : WithTop ℕ) at hx
      have ht : (τ x).untopD 0 = n := by rw [hx]; rfl
      dsimp only [f]
      rw [ht]
      exact sub_self _
    have hzero := condExp_ae_eq_restrict_zero hA hdiff
    have hsub := condExp_sub hstop (hgi n) (Filtration.piLE n)
    have hdet := condExp_selectedDescendantTrees K initial n (roots n) (hroots n) (hinj n)
      g hg (hgi n)
    have hs : P[f | hτ.measurableSpace] =ᵐ[P.restrict A] P[f | Filtration.piLE n] :=
      condExp_stopping_time_ae_eq_restrict_eq_of_countable (μ := P) hτ n (f := f)
    filter_upwards [hs, hzero, hsub.restrict, hdet.restrict, ae_restrict_mem hAm]
      with x hsx hzx hsubx hdetx hx
    change τ x = (n : WithTop ℕ) at hx
    have ht : (τ x).untopD 0 = n := by rw [hx]; rfl
    rw [hsx, ht]
    have heq : P[f | Filtration.piLE n] x =
        P[fun x => g (D n (frestrictLe n x, x)) | Filtration.piLE n] x :=
      sub_eq_zero.mp (hsubx.symm.trans hzx)
    exact heq.trans hdetx
  have hunion : (⋃ n : ℕ, {x | τ x = n}) = {x | τ x ≠ ⊤} := by
    ext x
    cases hval : τ x using WithTop.recTopCoe <;> simp [hval]
  simpa only [hunion] using hall

end ProbabilityTheory.BranchingProcess.State
