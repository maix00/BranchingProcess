/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Composition.InfinitePi
public import Probability.Kernel.Option
public import Probability.BranchingProcess.Offspring.Kernel
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Generation laws for state-dependent branching

## Public declarations

In namespace `ProbabilityTheory.BranchingProcess.State`:

* `generationKernel` maps a population state vector $s(r,u)$, $|u|=n$, to
  the next generation. Each present parent has offspring-state law $K(s)$,
  independently across parents; an absent parent has no children.
* `generationKernel_apply` identifies that next-population law as the
  measurable image of the independent offspring-family product.
* `generationKernel.isMarkovKernel` proves that this is a probability kernel.
* `generationKernel_broods` groups children by parent and recovers the law
  $\bigotimes_p K_\bot(s_p)$, including empty branches for absent parents.
* `generationHistoryKernel` takes a finite history and applies
  `generationKernel` to its last population state vector.
* `generationHistoryKernel.isMarkovKernel` proves it is a probability kernel.
* `generationPathLaw` is the Ionescu--Tulcea law of all generations from an
  arbitrary joint initial law on root states (which may be correlated).
* `generationPathLaw.isProbabilityMeasure` proves this is a probability law.
* `generationPathLaw_oneStep` identifies the joint law of the past and the
  next generation with the past law followed by the generation kernel:
  $P_{0:n}\otimes K_n=P\circ(X_{0:n},X_{n+1})^{-1}$.

The input is an arbitrary state-valued offspring probability kernel
$K:S\to\mathcal P(\mathrm{Step}(\alpha,S))$. For child marks with law
$Q(s,\cdot)$ and update $F$, use `offspringStateKernel F hF Q`.
No standard-Borel, additivity, or moment hypotheses are imposed.
The construction follows the parent-conditioned branching Markov property
of S. Valère Bitseki Penda and J.-F. Delmas, "Central limit theorem for
bifurcating Markov chains", Definition 2.1 (binary families),
https://cermics.gitlab.enpc.fr/delmas/Publi/clt-bmc-ptw.pdf,
and Mathlib's Ionescu--Tulcea construction (O. Kallenberg, *Foundations of
Modern Probability*, Theorem 8.24, third edition (2021),
DOI 10.1007/978-3-030-61871-1).
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

namespace ProbabilityTheory.BranchingProcess.State

/-- Draw independent offspring families at all current parents and read each
child at its extended address. A missing parent produces only missing children. -/
noncomputable def generationKernel {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (n : ℕ) :
    Kernel ((Root × (Fin n → α)) → Option S) ((Root × (Fin (n + 1) → α)) → Option S) :=
  (Kernel.infinitePi (fun p : Root × (Fin n → α) ↦
    (Kernel.optionElim (Measure.dirac (fun _ : α ↦ (none : Option S))) K).comap
      (fun x ↦ x p) (measurable_pi_apply p))).map
    (fun broods p ↦ broods (p.1, Fin.init p.2) (p.2 (Fin.last n)))

/-- The next population is the image of the independent parent-brood product law. -/
theorem generationKernel_apply {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (n : ℕ)
    (s : (Root × (Fin n → α)) → Option S) :
    generationKernel K n s =
      (Measure.infinitePi (fun p : Root × (Fin n → α) ↦
        (Kernel.optionElim (Measure.dirac (fun _ : α ↦ (none : Option S))) K) (s p))).map
        (fun broods p ↦ broods (p.1, Fin.init p.2) (p.2 (Fin.last n))) := by
  rw [generationKernel, Kernel.map_apply _ (by fun_prop)]
  rfl

instance generationKernel.isMarkovKernel {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (generationKernel (Root := Root) K n) := by
  unfold generationKernel
  apply Kernel.IsMarkovKernel.map
  apply measurable_pi_iff.mpr
  intro p
  exact (measurable_pi_apply (p.2 (Fin.last n))).comp
    (measurable_pi_apply (p.1, Fin.init p.2))

/-- Reading the next generation by parent and child slot recovers the
independent product of the state-dependent offspring laws. -/
theorem generationKernel_broods {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (n : ℕ)
    (s : (Root × (Fin n → α)) → Option S) :
    (generationKernel K n s).map (fun next p j ↦ next (p.1, Fin.snoc p.2 j)) =
      Measure.infinitePi (fun p : Root × (Fin n → α) ↦
        (Kernel.optionElim (Measure.dirac (fun _ : α ↦ (none : Option S))) K) (s p)) := by
  have hflatten : Measurable (fun broods : (Root × (Fin n → α)) → Step α S ↦
      fun p : Root × (Fin (n + 1) → α) ↦
        broods (p.1, Fin.init p.2) (p.2 (Fin.last n))) := by fun_prop
  have hgroup : Measurable (fun next : (Root × (Fin (n + 1) → α)) → Option S ↦
      fun p : Root × (Fin n → α) ↦ fun j ↦ next (p.1, Fin.snoc p.2 j)) := by fun_prop
  rw [generationKernel, Kernel.map_apply _ hflatten, Measure.map_map hgroup hflatten]
  have heq : (fun broods : (Root × (Fin n → α)) → Step α S ↦
      fun (p : Root × (Fin n → α)) (j : α) ↦
        broods (p.1, Fin.init (Fin.snoc p.2 j : Fin (n + 1) → α))
          ((Fin.snoc p.2 j : Fin (n + 1) → α) (Fin.last n))) = id := by
    funext broods p j
    simp
  change Measure.map
    (fun broods : (Root × (Fin n → α)) → Step α S ↦
      fun (p : Root × (Fin n → α)) (j : α) ↦
        broods (p.1, Fin.init (Fin.snoc p.2 j : Fin (n + 1) → α))
          ((Fin.snoc p.2 j : Fin (n + 1) → α) (Fin.last n)))
    (Measure.infinitePi (fun p ↦
      (Kernel.optionElim (Measure.dirac (fun _ : α ↦ (none : Option S))) K) (s p))) = _
  rw [heq, Measure.map_id]

/-- The next generation uses the last state vector in the observed history. -/
noncomputable def generationHistoryKernel {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (n : ℕ) :
    Kernel (Π k : Finset.Iic n, ((Root × (Fin k.1 → α)) → Option S))
      ((Root × (Fin (n + 1) → α)) → Option S) :=
  (generationKernel K n).comap (fun history ↦ history ⟨n, by simp⟩)
    (measurable_pi_apply (⟨n, by simp⟩ : Finset.Iic n))

instance generationHistoryKernel.isMarkovKernel {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (generationHistoryKernel (Root := Root) K n) := by
  unfold generationHistoryKernel
  infer_instance

/-- Law of the whole generation sequence from a joint root-state distribution. -/
noncomputable def generationPathLaw {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) :
    Measure (Π n : ℕ, ((Root × (Fin n → α)) → Option S)) :=
  Kernel.trajMeasure (initial.map (fun s p ↦ s p.1)) (generationHistoryKernel (Root := Root) K)

instance generationPathLaw.isProbabilityMeasure {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (generationPathLaw K initial) := by
  unfold generationPathLaw
  have : IsProbabilityMeasure (initial.map
      (fun (s : Root → Option S) (p : Root × (Fin 0 → α)) ↦ s p.1)) :=
    inferInstance
  infer_instance

/-- The canonical path law has precisely the prescribed conditional next-generation kernel. -/
theorem generationPathLaw_oneStep {Root α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial] (n : ℕ) :
    (generationPathLaw K initial).map (Preorder.frestrictLe n) ⊗ₘ
        generationHistoryKernel K n =
      (generationPathLaw K initial).map
        (fun x ↦ (Preorder.frestrictLe n x, x (n + 1))) := by
  unfold generationPathLaw
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end ProbabilityTheory.BranchingProcess.State
