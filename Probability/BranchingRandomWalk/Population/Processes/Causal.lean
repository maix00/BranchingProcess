import Probability.BranchingRandomWalk.Population.Processes.StepSelection.RootIndexed
import Combinatorics.BranchingWalk.Population.Genealogy

/-!
# Causal branching populations

A causal finite population records the genealogically labelled particles
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

end CausalPopulation

/-- A finite genealogically labelled population adapted to a generation
domain flow and obtained by causally killing genuine offspring.

No mechanism is stored: two different killing algorithms that produce the
same retained population define the same mathematical process. -/
structure CausalFinitePopulation
    (Ω Root α X : Type*) [MeasurableSpace Ω]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (stepField : Ω → RootIndexed.StepField Root α X) where
  toFinitePopulation : ∀ ω,
    Combinatorics.Branching.FinitePopulation (stepField ω)
  adapted : Adapted ℱ (fun n ω => toFinitePopulation ω n)

namespace CausalFinitePopulation

variable {Ω Root α X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    {ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}

instance : CoeFun (CausalFinitePopulation Ω Root α X ℱ stepField)
    (fun _ => ℕ → Ω → Finset (RootIndexed.TreeNode Root α)) :=
  ⟨fun P n ω => P.toFinitePopulation ω n⟩

theorem measurable (P : CausalFinitePopulation Ω Root α X ℱ stepField)
    (n : ℕ) : @Measurable Ω (Finset (RootIndexed.TreeNode Root α))
      (ℱ n) inferInstance (P n) :=
  P.adapted n

theorem mem_depth (P : CausalFinitePopulation Ω Root α X ℱ stepField)
    {n : ℕ} {ω : Ω} {p : RootIndexed.TreeNode Root α} (hp : p ∈ P n ω) :
    p.2.length = n :=
  (P.toFinitePopulation ω).depth n p hp

theorem depth (P : CausalFinitePopulation Ω Root α X ℱ stepField)
    (n : ℕ) (ω : Ω) (p : RootIndexed.TreeNode Root α)
    (hp : p ∈ P n ω) : p.2.length = n :=
  (P.toFinitePopulation ω).depth n p hp

theorem successor (P : CausalFinitePopulation Ω Root α X ℱ stepField)
    (n : ℕ) (ω : Ω) :
    ↑(P (n + 1) ω) ⊆
      Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        (↑(P n ω)) (fun p => support (stepField ω p.1 p.2)) :=
  (P.toFinitePopulation ω).successor n

/-- Forget finiteness while preserving the causal random-set structure. -/
def toCausalPopulation
    (P : CausalFinitePopulation Ω Root α X ℱ stepField) :
    CausalPopulation Ω Root α X ℱ stepField where
  toPopulation ω :=
    (P.toFinitePopulation ω).toPopulation
  adapted p n := (measurable_finset_mem p).comp (P.adapted n)

@[simp] theorem mem_toCausalPopulation
    (P : CausalFinitePopulation Ω Root α X ℱ stepField)
    (n : ℕ) (ω : Ω) (p : RootIndexed.TreeNode Root α) :
    p ∈ P.toCausalPopulation n ω ↔ p ∈ P n ω :=
  Iff.rfl

/-- Pull a causal population back along a map that is measurable at every
generation and intertwines the pre-sampled step fields.  This changes only
the sample-space realization; the retained genealogical population is
unchanged. -/
noncomputable def pullback
    {Ω' : Type*} [MeasurableSpace Ω']
    {ℱ' : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω')}
    {stepField' : Ω' → RootIndexed.StepField Root α X}
    (P : CausalFinitePopulation Ω' Root α X ℱ' stepField')
    (f : Ω → Ω')
    (hf : ∀ n, @Measurable Ω Ω' (ℱ n) (ℱ' n) f)
    (hfield : stepField' ∘ f = stepField) :
    CausalFinitePopulation Ω Root α X ℱ stepField where
  toFinitePopulation ω :=
    { particles := fun n => P n (f ω)
      depth := fun n p hp => P.depth n (f ω) p hp
      successor := fun n => by
        have hω : stepField' (f ω) = stepField ω := congrFun hfield ω
        rw [← hω]
        exact P.successor n (f ω) }
  adapted n := (P.adapted n).comp (hf n)

@[simp] theorem pullback_population
    {Ω' : Type*} [MeasurableSpace Ω']
    {ℱ' : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω')}
    {stepField' : Ω' → RootIndexed.StepField Root α X}
    (P : CausalFinitePopulation Ω' Root α X ℱ' stepField')
    (f : Ω → Ω')
    (hf : ∀ n, @Measurable Ω Ω' (ℱ n) (ℱ' n) f)
    (hfield : stepField' ∘ f = stepField) (n : ℕ) (ω : Ω) :
    P.pullback f hf hfield n ω = P n (f ω) :=
  rfl

/-- A population generated by one fixed finite selection at every node is a
causal finite population.  This constructor is a specialization theorem, not
the definition of causal killing. -/
noncomputable def ofStepSelectionOn
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (roots : Finset Root) :
    CausalFinitePopulation
      (RootIndexed.StepField Root α X) Root α X
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X)) id where
  toFinitePopulation field :=
    { particles := fun n =>
        RootIndexed.StepSelection.labelledPopulationOn R roots n field
      depth := fun n p hp =>
        RootIndexed.StepSelection.labelledPopulationOn_depth R roots n field hp
      successor := by
        intro n p hp
        have hselected :=
          RootIndexed.StepSelection.labelledPopulationOn_succ_subset
            R roots n field hp
        obtain ⟨parent, hparent, i, hi, rfl⟩ :=
          Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mp
            hselected
        apply Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mpr
        exact ⟨parent, hparent, i,
          R.mem_support (field parent.1 parent.2) hi, rfl⟩ }
  adapted := RootIndexed.StepSelection.labelledPopulationOn_adapted R hR roots

@[simp] theorem ofStepSelectionOn_population
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (roots : Finset Root) (n : ℕ)
    (field : RootIndexed.StepField Root α X) :
    ofStepSelectionOn R hR roots n field =
      RootIndexed.StepSelection.labelledPopulationOn R roots n field :=
  rfl

end CausalFinitePopulation
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
