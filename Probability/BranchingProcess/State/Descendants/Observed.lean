/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.BranchingProperty
public import Probability.Kernel.IonescuTulcea.Stopping

/-!
# Branching at nodes chosen from the observed history

## Public declarations

* `ProbabilityTheory.BranchingProcess.State.condExp_selectedDescendantTrees`:
  for distinct depth-$a$ addresses $R_i$ measurable in the generation history,
  $E[g((T_{R_i})_i)\mid\mathcal F_a]
    =\int g\,d\bigotimes_i P_{X_a(R_i)}$.
* `ProbabilityTheory.BranchingProcess.State.stopped_descendantTrees_condExp`
  proves the same formula on the finite-time event of any stopping time,
  with nodes selected
  from its observed history. Each fixed-time and stopped payoff is integrable.

  The initial root states may have any joint distribution, and the offspring
  law may depend on the parent state.

Root and child address spaces are countable with measurable singletons, to
ensure measurability of evaluation at a history-dependent address. The state
space is arbitrary measurable. Conditional independence is derived from the
constructed path law; it is not an assumption on the selected descendants.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

private lemma measurable_selectedDescendants {Root ι α S : Type*}
    [MeasurableSpace Root] [MeasurableSpace α] [MeasurableSpace S]
    [Countable Root] [Countable α]
    [MeasurableSingletonClass Root] [MeasurableSingletonClass α]
    (a : ℕ)
    (roots : (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) →
      ι → Root × (Fin a → α))
    (hroots : ∀ i, Measurable (fun h ↦ roots h i)) :
    Measurable (fun p : (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) ×
        (Π n : ℕ, (Root × (Fin n → α)) → Option S) ↦
      fun i (u : List α) ↦ p.2 (a + u.length)
        ((roots p.1 i).1, Fin.append (roots p.1 i).2 u.get)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro u
  have he : Measurable (fun p :
      (Π n : ℕ, (Root × (Fin n → α)) → Option S) × (Root × (Fin a → α)) ↦
      p.1 (a + u.length) (p.2.1, Fin.append p.2.2 u.get)) :=
    measurable_from_prod_countable_left (fun r ↦
      (measurable_pi_apply (r.1, Fin.append r.2 u.get)).comp
        (measurable_pi_apply (a + u.length)))
  exact he.comp (measurable_snd.prodMk ((hroots i).comp measurable_fst))

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
  let D (p : (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) ×
      (Π n : ℕ, (Root × (Fin n → α)) → Option S)) i (u : List α) :=
    p.2 (a + u.length) ((roots p.1 i).1, Fin.append (roots p.1 i).2 u.get)
  have hD : Measurable D := measurable_selectedDescendants a roots hroots
  have hj : (generationPathLaw K initial).map
      (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦ (frestrictLe a x, x)) =
      (generationPathLaw K initial).map (frestrictLe a) ⊗ₘ
        Kernel.traj (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
          (generationHistoryKernel (Root := Root) K) a := by
    unfold generationPathLaw
    exact (Kernel.trajMeasure_compProd_traj
      (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
      (generationHistoryKernel (Root := Root) K)
      (initial.map (fun (s : Root → Option S) (p : Root × (Fin 0 → α)) ↦ s p.1)) a).symm
  have hc := Kernel.condExp_of_jointLaw (E := E) (generationPathLaw K initial)
    (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S ↦ frestrictLe a x)
    (id : (Π n : ℕ, (Root × (Fin n → α)) → Option S) → _)
    (measurable_frestrictLe a) measurable_id
    (Kernel.traj (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
      (generationHistoryKernel (Root := Root) K) a) hj
    (g := g ∘ D) (hg.comp_measurable hD) hgi
  rw [Filtration.piLE_eq_comap_frestrictLe]
  filter_upwards [hc] with x hx
  have ht := congrArg (fun μ ↦ ∫ trees, g trees ∂μ)
    (traj_descendantTrees K a (frestrictLe a x)
      (roots (frestrictLe a x)) (hinj _))
  have hi := integral_map (μ := Kernel.traj
    (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
    (generationHistoryKernel (Root := Root) K) a (frestrictLe a x))
    (φ := fun y ↦ D (frestrictLe a x, y))
    (hD.comp (measurable_const.prodMk measurable_id)).aemeasurable
    hg.aestronglyMeasurable
  exact hx.trans (hi.symm.trans ht)

/-- State-dependent branching on the finite-time event of a stopping generation, including
nodes chosen from the observed history. The proof uses the deterministic
branching identity on each event $\{\tau=n\}$. -/
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
  unfold generationPathLaw at hgi hstop ⊢
  have hD (a : ℕ) : Measurable (D a) :=
    measurable_selectedDescendants a (roots a) (hroots a)
  have hgD (a : ℕ) : StronglyMeasurable (fun p :
      (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) ×
        (Π n : ℕ, (Root × (Fin n → α)) → Option S) ↦ g (D a p)) :=
    hg.comp_measurable (hD a)
  have hc := Kernel.condExp_trajMeasure_stopping
    (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
    (generationHistoryKernel (Root := Root) K)
    (initial.map (fun (s : Root → Option S) (p : Root × (Fin 0 → α)) ↦ s p.1)) τ hτ
    (fun a (p : (Π k : Iic a, (Root × (Fin k.1 → α)) → Option S) ×
      (Π n : ℕ, (Root × (Fin n → α)) → Option S)) ↦ g (D a p))
    hgD hgi hstop
  filter_upwards [hc] with x hx
  have ht := congrArg (fun μ ↦ ∫ trees, g trees ∂μ)
    (traj_descendantTrees K ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x)
      (roots ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x)) (hinj _ _))
  have hi := integral_map (μ := Kernel.traj
    (X := fun n : ℕ ↦ (Root × (Fin n → α)) → Option S)
    (generationHistoryKernel (Root := Root) K) ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x))
    (φ := fun y ↦ D ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, y))
    ((hD ((τ x).untopD 0)).comp (measurable_const.prodMk measurable_id)).aemeasurable
    hg.aestronglyMeasurable
  exact hx.trans (hi.symm.trans ht)

end ProbabilityTheory.BranchingProcess.State
