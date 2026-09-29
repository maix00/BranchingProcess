module

public import Probability.BranchingRandomWalk.Population.Processes.StepSelection.RootIndexed
public import Combinatorics.BranchingWalk.Population.Genealogy

/-!
# Causal branching populations

A causal population records the genealogically labelled particles
retained at every generation.  Retention may use the whole available
generation domain and may vary by generation.  The only structural requirement is
that every successor is a genuine child of a retained parent in the supplied
pre-sampled step field.

This is the process-level abstraction for killed branching random walks.
Local, time-homogeneous `Step.FiniteSelection` processes are a special case.
The index is the intrinsic natural-number generation of the branching tree;
it is not a separate discrete-time dynamics layered over the tree.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching

attribute [local instance] Classical.propDecidable Classical.decEq

/-- A set-valued branching population adapted to a generation domain flow
and closed under genuine parent-child succession.

No finiteness or countability is imposed.  Measurability is stated
coordinatewise through membership events, which is the natural interface for
arbitrary random sets. -/
structure CausalPopulation
    (Ω Root α X : Type*) [MeasurableSpace Ω]
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (stepField : Ω → RootIndexed.StepField Root α X) where
  toPopulation : ∀ ω, Combinatorics.Branching.Population (stepField ω)
  adapted : ∀ p, Adapted ℱ (fun n ω => p ∈ toPopulation ω n)

namespace CausalPopulation

variable {Ω Root α X : Type*} [MeasurableSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}

instance : CoeFun (CausalPopulation Ω Root α X ℱ stepField)
    (fun _ => ℕ → Ω → Set (RootIndexed.TreeNode Root α)) :=
  ⟨fun P n ω => P.toPopulation ω n⟩

theorem measurable_mem
    (P : CausalPopulation Ω Root α X ℱ stepField) (n : ℕ)
    (p : RootIndexed.TreeNode Root α) :
    @Measurable Ω Prop (ℱ n) inferInstance (fun ω => p ∈ P n ω) :=
  P.adapted p n

theorem depth (P : CausalPopulation Ω Root α X ℱ stepField)
    (n : ℕ) (ω : Ω) (p : RootIndexed.TreeNode Root α)
    (hp : p ∈ P n ω) : p.2.length = n :=
  (P.toPopulation ω).depth n p hp

theorem successor (P : CausalPopulation Ω Root α X ℱ stepField)
    (n : ℕ) (ω : Ω) :
    P (n + 1) ω ⊆
      Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        (P n ω) (fun p => support (stepField ω p.1 p.2)) :=
  (P.toPopulation ω).successor n

/-- Pull a causal population back along a map that is measurable at every
generation and intertwines the pre-sampled step fields. -/
noncomputable def pullback
    {Ω' : Type*} [MeasurableSpace Ω']
    {ℱ' : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω')}
    {stepField' : Ω' → RootIndexed.StepField Root α X}
    (P : CausalPopulation Ω' Root α X ℱ' stepField')
    (f : Ω → Ω')
    (hf : ∀ n, @Measurable Ω Ω' (ℱ n) (ℱ' n) f)
    (hfield : stepField' ∘ f = stepField) :
    CausalPopulation Ω Root α X ℱ stepField where
  toPopulation ω :=
    { particles := fun n => P n (f ω)
      depth := fun n p hp => P.depth n (f ω) p hp
      successor := fun n => by
        have hω : stepField' (f ω) = stepField ω := congrFun hfield ω
        rw [← hω]
        exact P.successor n (f ω) }
  adapted p n := (P.adapted p n).comp (hf n)

@[simp] theorem pullback_population
    {Ω' : Type*} [MeasurableSpace Ω']
    {ℱ' : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω')}
    {stepField' : Ω' → RootIndexed.StepField Root α X}
    (P : CausalPopulation Ω' Root α X ℱ' stepField')
    (f : Ω → Ω')
    (hf : ∀ n, @Measurable Ω Ω' (ℱ n) (ℱ' n) f)
    (hfield : stepField' ∘ f = stepField) (n : ℕ) (ω : Ω) :
    P.pullback f hf hfield n ω = P n (f ω) :=
  rfl

/-- Layerwise finiteness is a property of the set-valued process. -/
def FiniteSlices (P : CausalPopulation Ω Root α X ℱ stepField) : Prop :=
  ∀ n ω, (P n ω).Finite

namespace FiniteSlices

theorem pullback
    {Ω' : Type*} [MeasurableSpace Ω']
    {ℱ' : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω')}
    {stepField' : Ω' → RootIndexed.StepField Root α X}
    {P : CausalPopulation Ω' Root α X ℱ' stepField'}
    (hP : P.FiniteSlices) (f : Ω → Ω')
    (hf : ∀ n, @Measurable Ω Ω' (ℱ n) (ℱ' n) f)
    (hfield : stepField' ∘ f = stepField) :
    (P.pullback f hf hfield).FiniteSlices :=
  fun n ω => hP n (f ω)

/-- Obtain a `Finset` only at the finite slice where it is required. -/
noncomputable def toFinset
    {P : CausalPopulation Ω Root α X ℱ stepField}
    (hP : P.FiniteSlices) (n : ℕ) (ω : Ω) :
    Finset (RootIndexed.TreeNode Root α) :=
  (hP n ω).toFinset

@[simp] theorem mem_toFinset
    {P : CausalPopulation Ω Root α X ℱ stepField}
    (hP : P.FiniteSlices) (n : ℕ) (ω : Ω)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ hP.toFinset n ω ↔ p ∈ P n ω :=
  Set.Finite.mem_toFinset _

@[simp] theorem coe_toFinset
    {P : CausalPopulation Ω Root α X ℱ stepField}
    (hP : P.FiniteSlices) (n : ℕ) (ω : Ω) :
    ↑(hP.toFinset n ω) = P n ω :=
  Set.Finite.coe_toFinset _

/-- Finite presentation of a slice remains measurable.  This theorem is the
bridge for algorithms whose output data is necessarily a `Finset`; the
population itself remains set-valued. -/
theorem measurable_toFinset
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    {P : CausalPopulation Ω Root α X ℱ stepField}
    (hP : P.FiniteSlices) (n : ℕ) :
    @Measurable Ω (Finset (RootIndexed.TreeNode Root α))
      (ℱ n) inferInstance (hP.toFinset n) := by
  apply (@measurable_finset_iff
    (RootIndexed.TreeNode Root α) Ω (ℱ n)).2
  intro p
  simpa only [mem_toFinset] using P.adapted p n

end FiniteSlices

end CausalPopulation

end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
