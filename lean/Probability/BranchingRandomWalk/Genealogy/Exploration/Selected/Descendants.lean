import Probability.BranchingRandomWalk.Population.Processes.Selected
import MeasureTheory.BranchingWalk.Position.Increment
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Independence

/-!
# Descendants of a finite selected population

The number of particles kept by the common multi-root selection can be
random. On the event that the selected generation is a particular finite set,
its elements can be listed by a fixed vector. This file records that listing,
the dependent descendant population of a fixed root vector, and the
translated positions of those descendants. The branching laws on the cells of
that listing are in `Selected/CellBranching.lean`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory.BranchingWalk MeasureTheory



/-! A descendant walk is obtained by reading the marked tree below a listed
root and retaining the initial spatial offset.  Keeping this map explicit
prevents the branching statement from silently dropping the root position. -/
def multiRootTranslatedPosition {m k : ℕ}
    (x : Fin m → ℝ) (roots : Fin k → RootAddress m)
    (ω : FiniteRootStepField m ℝ) (j : Fin k) (v : 𝕍) : ℝ :=
  rootIndexedNodePosition x ω (roots j).1 ((roots j).2 ++ v)

/-! A dependent finite descendant population.  The index `k` is part of the
    object, so a random population size is represented by a sigma-type rather
    than by padding a fixed vector with dummy roots. -/
structure FiniteDescendantPopulation (m : ℕ) (X : Type*) where
  size : ℕ
  roots : Fin size → RootAddress m
  roots_injective : Function.Injective roots
  field : Fin size → 𝕍 → Step ℕ X

def FiniteDescendantPopulation.absolutePosition {m : ℕ}
    (x : Fin m → ℝ) (P : FiniteDescendantPopulation m ℝ)
    (ω : FiniteRootStepField m ℝ) (j : Fin P.size) (v : 𝕍) : ℝ :=
  rootIndexedNodePosition x ω (P.roots j).1 ((P.roots j).2 ++ v)

def FiniteDescendantPopulation.fromRoots {m k : ℕ} {X : Type*}
    (roots : Fin k → RootAddress m)
    (hinj : Function.Injective roots)
    (step : FiniteRootStepField m X) :
    FiniteDescendantPopulation m X where
  size := k
  roots := roots
  roots_injective := hinj
  field := multiRootSubtreeStepFieldVector roots step

@[simp] theorem FiniteDescendantPopulation.fromRoots_size
    {m k : ℕ} {X : Type*}
    (roots : Fin k → RootAddress m) (hinj : Function.Injective roots)
    (step : FiniteRootStepField m X) :
    (FiniteDescendantPopulation.fromRoots roots hinj step).size = k := rfl

theorem FiniteDescendantPopulation.fromRoots_field
    {m k : ℕ} {X : Type*}
    (roots : Fin k → RootAddress m) (hinj : Function.Injective roots)
    (step : FiniteRootStepField m X) (j : Fin k) (v : 𝕍) :
    (FiniteDescendantPopulation.fromRoots roots hinj step).field j v =
      step (roots j).1 ((roots j).2 ++ v) := rfl

theorem FiniteDescendantPopulation.fromRoots_absolutePosition
    {m k : ℕ} (x : Fin m → ℝ)
    (roots : Fin k → RootAddress m) (hinj : Function.Injective roots)
    (step : FiniteRootStepField m ℝ)
    (ω : FiniteRootStepField m ℝ) (j : Fin k) (v : 𝕍) :
    (FiniteDescendantPopulation.fromRoots roots hinj step).absolutePosition
        x ω j v =
      rootIndexedNodePosition x ω (roots j).1 ((roots j).2 ++ v) := rfl

theorem FiniteDescendantPopulation.absolutePosition_at_root
    {m : ℕ} (x : Fin m → ℝ) (P : FiniteDescendantPopulation m ℝ)
    (ω : FiniteRootStepField m ℝ) (j : Fin P.size) :
    P.absolutePosition x ω j [] =
      rootIndexedNodePosition x ω (P.roots j).1 (P.roots j).2 := by
  simp [FiniteDescendantPopulation.absolutePosition]

theorem FiniteDescendantPopulation.absolutePosition_child
    {m : ℕ} (x : Fin m → ℝ) (P : FiniteDescendantPopulation m ℝ)
    (ω : FiniteRootStepField m ℝ) (j : Fin P.size)
    (v : 𝕍) (i : ℕ) :
    P.absolutePosition x ω j (v ++ [i]) =
      P.absolutePosition x ω j v +
        value (ω (P.roots j).1 ((P.roots j).2 ++ v)) i := by
  unfold FiniteDescendantPopulation.absolutePosition
  rw [← List.append_assoc, rootIndexedNodePosition_append_singleton]

theorem FiniteDescendantPopulation.fromRoots_localPathSum
    {m k : ℕ} (roots : Fin k → RootAddress m)
    (hinj : Function.Injective roots)
    (step : FiniteRootStepField m ℝ)
    (j : Fin k) (v : 𝕍) :
    displaceRoot
        ((FiniteDescendantPopulation.fromRoots roots hinj step).field j) v =
      displaceRoot (fun w =>
        step (roots j).1 ((roots j).2 ++ w)) v := by
  rfl

theorem FiniteDescendantPopulation.fromRoots_position_decomposition
    {m k : ℕ} (x : Fin m → ℝ)
    (roots : Fin k → RootAddress m) (hinj : Function.Injective roots)
    (step : FiniteRootStepField m ℝ)
    (ω : FiniteRootStepField m ℝ) (j : Fin k) (v : 𝕍) :
    (FiniteDescendantPopulation.fromRoots roots hinj step).absolutePosition
        x ω j v =
      (FiniteDescendantPopulation.fromRoots roots hinj step).absolutePosition
        x ω j [] +
        displaceRoot (fun w =>
          ω (roots j).1 ((roots j).2 ++ w)) v := by
  simp only [FiniteDescendantPopulation.absolutePosition,
    FiniteDescendantPopulation.fromRoots, List.append_nil]
  exact rootIndexedNodePosition_append x ω (roots j).1 (roots j).2 v

noncomputable def FiniteDescendantPopulation.fromSelected
    {m : ℕ} (s : Finset (RootAddress m))
    (step : FiniteRootStepField m ℝ) :
    FiniteDescendantPopulation m ℝ :=
  let e : {p : RootAddress m // p ∈ s} ≃ Fin s.card :=
    Fintype.equivFinOfCardEq (by simp)
  FiniteDescendantPopulation.fromRoots
    (fun j => (e.symm j).1) (by
      intro i j hij
      apply e.symm.injective
      exact Subtype.ext hij) step

theorem multiRootTranslatedPosition_measurable {m k : ℕ}
    (x : Fin m → ℝ) (roots : Fin k → RootAddress m)
    (j : Fin k) (v : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) ((roots j).2 ++ v).length]
      (fun ω : FiniteRootStepField m ℝ =>
        multiRootTranslatedPosition x roots ω j v) := by
  exact rootIndexedNodePosition_measurable x (roots j).1 ((roots j).2 ++ v)

theorem multiRootTranslatedPosition_at_root {m k : ℕ}
    (x : Fin m → ℝ) (roots : Fin k → RootAddress m)
    (ω : FiniteRootStepField m ℝ) (j : Fin k) :
    multiRootTranslatedPosition x roots ω j [] =
      rootIndexedNodePosition x ω (roots j).1 (roots j).2 := by
  simp [multiRootTranslatedPosition]

theorem multiRootTranslatedPosition_vector_measurable {m k n : ℕ}
    (x : Fin m → ℝ) (roots : Fin k → RootAddress m)
    (hlen : ∀ j, (roots j).2.length = n) (v : 𝕍) :
    Measurable[multiRootStepFiltration (m := m) (X := ℝ) (n + v.length)]
      (fun ω : FiniteRootStepField m ℝ =>
        fun j : Fin k => multiRootTranslatedPosition x roots ω j v) := by
  apply (@measurable_pi_iff (FiniteRootStepField m ℝ) (Fin k)
    (fun _ => ℝ) (multiRootStepFiltration (m := m) (X := ℝ) (n + v.length))
    (fun _ => inferInstance) _).2
  intro j
  unfold multiRootTranslatedPosition
  have hj : ((roots j).2 ++ v).length = n + v.length := by
    simp [hlen j, Nat.add_comm]
  convert rootIndexedNodePosition_measurable x (roots j).1 ((roots j).2 ++ v) using 1
  exact congrArg (fun r => multiRootStepFiltration (m := m) (X := ℝ) r) hj.symm

theorem multiRootTranslatedPosition_child {m k : ℕ}
    (x : Fin m → ℝ) (roots : Fin k → RootAddress m)
    (ω : FiniteRootStepField m ℝ) (j : Fin k) (v : 𝕍) (i : ℕ) :
    multiRootTranslatedPosition x roots ω j (v ++ [i]) =
      multiRootTranslatedPosition x roots ω j v +
        value (ω (roots j).1 ((roots j).2 ++ v)) i := by
  unfold multiRootTranslatedPosition
  rw [← List.append_assoc, rootIndexedNodePosition_append_singleton]

end ProbabilityTheory.BranchingRandomWalk
