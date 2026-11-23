import Probability.BranchingProcess.State.Descendants.Observed

open MeasureTheory ProbabilityTheory Combinatorics.Branching
open ProbabilityTheory.BranchingProcess.State

-- A genuine state-dependent law: false is sterile, true has two child slots.
private noncomputable def typeOffspring : Kernel Bool (Step Bool Bool) :=
  Kernel.deterministic (fun s j ↦ if s then some j else none)
    (measurable_of_countable _)

private instance : IsMarkovKernel typeOffspring := by
  unfold typeOffspring
  infer_instance

example : typeOffspring false = Measure.dirac (fun _ : Bool ↦ (none : Option Bool)) := rfl
example : typeOffspring true = Measure.dirac (fun j : Bool ↦ some j) := rfl

-- The complete process exists from correlated initial root states, not only
-- from a deterministic initial vector or a product initial law.
example {Root : Type*} (initial : Measure (Root → Option Bool))
    [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (generationPathLaw typeOffspring initial) := inferInstance

-- The root marginal is preserved for a nonconstant offspring law.
example (s : Option Bool) :
    (treeKernel typeOffspring s).map (fun t ↦ t []) = Measure.dirac s :=
  treeKernel_root typeOffspring s

-- General mark kernels and nonadditive updates feed the same process API.
example {Root Mark S : Type*} [MeasurableSpace Mark] [MeasurableSpace S]
    (Q : Kernel S (Step Bool Mark)) [IsMarkovKernel Q]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F))
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure
      (generationPathLaw (BranchingProcess.offspringStateKernel F hF Q) initial) :=
  inferInstance

-- The branching identity applies to complete infinite trees, on arbitrary
-- measurable state spaces, without moments, normalization, or a state order.
example {Root ι α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (a : ℕ)
    (h : Π k : Finset.Iic a, (Root × (Fin k.1 → α)) → Option S)
    (r : ι → Root × (Fin a → α)) (hr : Function.Injective r) :
    (Kernel.traj (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
        (generationHistoryKernel K) a h).map
      (fun x i (u : List α) ↦ x (a + u.length) ((r i).1, Fin.append (r i).2 u.get)) =
      Measure.infinitePi (fun i ↦ treeKernel K (h ⟨a, by simp⟩ (r i))) :=
  traj_descendantTrees K a h r hr

#print axioms ProbabilityTheory.Kernel.infinitePi_compProd
#print axioms ProbabilityTheory.Kernel.trajMeasure_infinitePi
#print axioms ProbabilityTheory.Kernel.map_traj_eq_trajMeasure
#print axioms ProbabilityTheory.Kernel.condExp_of_jointLaw
#print axioms ProbabilityTheory.BranchingProcess.State.generationPathLaw_oneStep
#print axioms ProbabilityTheory.BranchingProcess.State.traj_descendantTrees
#print axioms ProbabilityTheory.BranchingProcess.State.condExp_descendantTrees
#print axioms ProbabilityTheory.BranchingProcess.State.condExp_selectedDescendantTrees

#print axioms ProbabilityTheory.BranchingProcess.State.stopped_descendantTrees_condExp
