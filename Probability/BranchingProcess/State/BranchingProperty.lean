/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Descendants.Path
public import Probability.Kernel.IonescuTulcea.Conditional

/-!
# Branching property for state-dependent offspring laws

## Public declarations

In namespace `ProbabilityTheory.BranchingProcess.State`:

* `traj_descendantTrees` identifies the complete descendant-tree law after
  a specified generation history:
  $\operatorname{Law}((T_{r_i,u_i})_i\mid\text{history})
    =\bigotimes_i P_{X_a(r_i,u_i)}$ for distinct depth-$a$ addresses.
* `descendantTrees_jointLaw` gives the joint-measure disintegration
  `Law(history, (Tᵢ)ᵢ) = Law(history) ⊗ (⊗ᵢ P_(Xₐ(rᵢ,uᵢ)))`.
  It allows arbitrary joint initial root states and measurable payoff functions
  without an integrability condition on those payoffs.
* `condExp_descendantTrees` gives the equivalent conditional-integral identity
  under the actual process law with any joint initial distribution:
  $E[g((T_{r_i,u_i})_i)\mid\mathcal F_a]
    =\int g\,d\bigotimes_i P_{X_a(r_i,u_i)}$.

Here $P_s$ is `treeKernel K s`, constructed from the same arbitrary
state-dependent offspring kernel $K$. For mark law $Q$ and measurable update
$F$, put $K=\texttt{offspringStateKernel}\ F\ Q$. No additivity, normalization,
order, moment, or standard-Borel assumptions are needed. Root states may
have an arbitrary joint distribution.

The proof extends the independent parent-conditioned reproduction laws to
finite descendant depths and then to the full tree sigma algebra by
Ionescu--Tulcea uniqueness. Compare S. Valère Bitseki Penda and J.-F. Delmas,
"Central limit theorem for bifurcating Markov chains", Definition 2.1
(binary families), https://cermics.gitlab.enpc.fr/delmas/Publi/clt-bmc-ptw.pdf.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

/-- Full descendant-tree independence conditional on the specified finite history. -/
theorem traj_descendantTrees {Root ι α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (a : ℕ)
    (history : Π k : Iic a, (Root × (Fin k.1 → α)) → Option S)
    (roots : ι → Root × (Fin a → α)) (hinj : Function.Injective roots) :
    (Kernel.traj (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
        (generationHistoryKernel K) a history).map
        (fun x i (u : List α) ↦
          x (a + u.length) ((roots i).1, Fin.append (roots i).2 u.get)) =
      Measure.infinitePi (fun i ↦ treeKernel K (history ⟨a, by simp⟩ (roots i))) := by
  have h := congrArg (fun μ ↦ μ.map
    (fun paths i (u : List α) ↦ paths u.length i ((), u.get)))
    (traj_descendantPaths K a history roots hinj)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  simp only [Function.comp_def] at h
  rw [h]
  calc
    _ = Measure.infinitePi (fun i ↦
        (pathKernel K (history ⟨a, by simp⟩ (roots i))).map
          (fun x (u : List α) ↦ x u.length ((), u.get))) :=
      Measure.infinitePi_map_pi _ (fun _ ↦ by fun_prop)
    _ = _ := by
      congr 1
      funext i
      rw [treeKernel, Kernel.map_apply _ (by fun_prop)]

/-- Joint disintegration of the observed history and the complete descendant-tree family. -/
theorem descendantTrees_jointLaw {Root ι α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    (a : ℕ) (roots : ι → Root × (Fin a → α)) (hinj : Function.Injective roots) :
    (generationPathLaw K initial).map (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S =>
      (frestrictLe a x,
      fun i (u : List α) =>
        x (a + u.length) ((roots i).1, Fin.append (roots i).2 u.get))) =
      (generationPathLaw K initial).map (frestrictLe a) ⊗ₘ
        Kernel.infinitePi (fun i => (treeKernel K).comap
          (fun history : Π k : Iic a, (Root × (Fin k.1 → α)) → Option S =>
            history ⟨a, by simp⟩ (roots i)) (by fun_prop)) := by
  let D (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) i (u : List α) :=
    x (a + u.length) ((roots i).1, Fin.append (roots i).2 u.get)
  have hD : Measurable D := by fun_prop
  have hm : (Kernel.traj
      (X := fun n : ℕ => (Root × (Fin n → α)) → Option S)
      (generationHistoryKernel (Root := Root) K) a).map D =
      Kernel.infinitePi (fun i => (treeKernel K).comap
        (fun history : Π k : Iic a, (Root × (Fin k.1 → α)) → Option S =>
          history ⟨a, by simp⟩ (roots i)) (by fun_prop)) := by
    apply Kernel.ext
    intro history
    rw [Kernel.map_apply _ hD, Kernel.infinitePi_apply]
    exact traj_descendantTrees K a history roots hinj
  unfold generationPathLaw
  rw [← hm, Measure.compProd_map hD, Kernel.trajMeasure_compProd_traj,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

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
  have hD : Measurable (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S =>
      fun i (u : List α) =>
        x (a + u.length) ((roots i).1, Fin.append (roots i).2 u.get)) := by fun_prop
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact Kernel.condExp_of_jointLaw (generationPathLaw K initial)
    (frestrictLe a) _ (measurable_frestrictLe a) hD
    (Kernel.infinitePi (fun i => (treeKernel K).comap
      (fun history : Π k : Iic a, (Root × (Fin k.1 → α)) → Option S =>
        history ⟨a, by simp⟩ (roots i)) (by fun_prop)))
    (descendantTrees_jointLaw K initial a roots hinj)
    (hg.comp_measurable measurable_snd) hgi

end ProbabilityTheory.BranchingProcess.State

end
