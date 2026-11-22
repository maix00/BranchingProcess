/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Kernel
public import Probability.BranchingProcess.Offspring.FieldLaw
public import MeasureTheory.BranchingWalk.MarkedTree
import Mathlib.Probability.Independence.Basic

/-!
# Realizing the canonical state process on an independent offspring field

## Public declarations

* `ProbabilityTheory.BranchingProcess.State.map_stateTree_offspringFieldLaw` identifies
  the realized tree from an independent mark field with the canonical kernel:
  $(\bigotimes_u\mu)\circ V_{F,s}^{-1}
    =P_{\operatorname{some}(s)}^{Q^F}$, where $Q(x)=\mu$.

There is one state-tree kernel, `treeKernel`. This theorem identifies its
independent-field realization in the constant mark-law case. The proof checks
its initial and conditional next-generation laws, then uses Ionescu--Tulcea
uniqueness (O. Kallenberg, *Foundations of Modern Probability*, third edition,
2021, Theorem 8.24, DOI 10.1007/978-3-030-61871-1).
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

private def updateBrood {α Mark S : Type*} (F : S → Mark → S)
    (s : Option S) (b : Step α Mark) : Step α S :=
  s.elim (fun _ ↦ none) (fun x ↦ b.map (F x))

private lemma updateBrood_measurable {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun p : Option S × Step α Mark ↦ updateBrood F p.1 p.2) := by
  exact measurable_fst.option_elim measurable_const
    ((Step.map_state_measurable (α := α) F hF).comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

private lemma updateBrood_law {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (s : Option S) :
    μ.map (updateBrood F s) =
      Kernel.optionElim (Measure.dirac (fun _ : α ↦ (none : Option S)))
        (offspringStateKernel F hF (Kernel.const S μ)) s := by
  cases s with
  | none =>
    change μ.map (fun _ ↦ (fun _ : α ↦ (none : Option S))) = _
    simp
  | some x =>
    rw [Kernel.optionElim_some, offspringStateKernel_apply, Kernel.const_apply]
    rfl

private noncomputable def fieldStatePath {α Mark S : Type*} (F : S → Mark → S) (s : S)
    (β : StepField α Mark) (n : ℕ) (p : Unit × (Fin n → α)) : Option S :=
  stateTree F s β (List.ofFn p.2)

private lemma fieldStatePath_measurable {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (s : S) :
    Measurable (fieldStatePath (α := α) F s) := by
  apply measurable_pi_iff.mpr
  intro n
  apply measurable_pi_iff.mpr
  intro p
  exact (measurable_pi_apply (List.ofFn p.2)).comp
    ((stateTree_measurable F hF).comp (measurable_const.prodMk measurable_id))

private lemma updateGeneration_law {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (n : ℕ)
    (s : (Unit × (Fin n → α)) → Option S) :
    (Measure.infinitePi (fun _ : Unit × (Fin n → α) ↦ μ)).map
      (fun broods (p : Unit × (Fin (n + 1) → α)) ↦
        updateBrood F (s (p.1, Fin.init p.2)) (broods (p.1, Fin.init p.2))
          (p.2 (Fin.last n))) =
      generationKernel (offspringStateKernel F hF (Kernel.const S μ)) n s := by
  rw [generationKernel_apply]
  simp_rw [← updateBrood_law μ F hF]
  have hpi := Measure.infinitePi_map_pi
    (fun _ : Unit × (Fin n → α) ↦ μ)
    (f := fun p ↦ updateBrood F (s p))
    (fun p ↦ (updateBrood_measurable F hF).comp
      (measurable_const.prodMk measurable_id))
  have hm : Measurable (fun broods : (Unit × (Fin n → α)) → Step α Mark ↦
      fun p ↦ updateBrood F (s p) (broods p)) :=
    measurable_pi_iff.mpr fun p ↦ (updateBrood_measurable F hF).comp
      (measurable_const.prodMk (measurable_pi_apply p))
  rw [← hpi, Measure.map_map (by fun_prop) hm]
  rfl

private lemma fieldPrefix_measurable {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (s : S) (n : ℕ) :
    Measurable[MeasurableSpace.comap
      (fun β : StepField α Mark ↦ fun u : {u : List α // u.length < n} ↦ β u.1)
      inferInstance] (fun β ↦ frestrictLe n (fieldStatePath F s β)) := by
  let past := MeasurableSpace.comap
    (fun β : StepField α Mark ↦ fun u : {u : List α // u.length < n} ↦ β u.1)
      inferInstance
  let : MeasurableSpace (StepField α Mark) := past
  have hrest : Measurable[past]
      (fun β : StepField α Mark ↦ fun u : {u : List α // u.length < n} ↦ β u.1) :=
    Measurable.of_comap_le le_rfl
  have hcoord (u : List α) (hu : u.length < n) :
      Measurable[past] (fun β : StepField α Mark ↦ β u) :=
    (measurable_pi_apply (⟨u, hu⟩ : {u : List α // u.length < n})).comp
      hrest
  have hsurv : ∀ (v p : List α), v.length + p.length ≤ n →
      MeasurableSet[past] {β : StepField α Mark | surviveAlong β v p} := by
    intro v p
    induction p generalizing v with
    | nil => intro _; exact MeasurableSet.univ
    | cons j p ih =>
      intro hp
      have hv : v.length < n := by simp only [List.length_cons] at hp; omega
      exact ((survive_measurableSet j).preimage (hcoord v hv)).inter
        (ih (v ++ [j]) (by
          simp only [List.length_append, List.length_singleton]
          simp only [List.length_cons] at hp
          omega))
  apply measurable_pi_iff.mpr
  intro k
  apply measurable_pi_iff.mpr
  intro p
  let u := List.ofFn p.2
  have hu : u.length ≤ n := by simpa [u] using mem_Iic.mp k.2
  have hstate : Measurable[past] (fun β : StepField α Mark ↦ stateAlong F β s [] u) := by
    exact stateAlong_measurable F hF id (fun _ ↦ s) [] u measurable_const
      (fun j hj ↦ (measurable_pi_apply (u[j])).comp
        (hcoord (u.take j) (by simp only [List.length_take]; omega)))
  exact (measurable_option_some.comp hstate).ite
    (hsurv [] u (by simpa using hu)) measurable_const

private lemma fieldPrefix_broods_independent {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (s : S) (n : ℕ) :
    IndepFun (fun β ↦ frestrictLe n (fieldStatePath F s β))
      (fun β (p : Unit × (Fin n → α)) ↦ β (List.ofFn p.2)) (offspringFieldLaw μ) := by
  let A := {u : List α | u.length < n}
  let B := {u : List α | u.length = n}
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    change u.length < n at hu
    change u.length = n at hv
    omega
  have hi := iIndepFun.indepFun_set A B hdisj (offspringFieldLaw_independent μ)
    (fun u ↦ measurable_pi_apply u)
  have hB : Measurable[MeasurableSpace.comap
      (fun β : StepField α Mark ↦ fun u : B ↦ β u.1) inferInstance]
      (fun β (p : Unit × (Fin n → α)) ↦ β (List.ofFn p.2)) := by
    let : MeasurableSpace (StepField α Mark) := MeasurableSpace.comap
      (fun β : StepField α Mark ↦ fun u : B ↦ β u.1) inferInstance
    have hrest : Measurable
        (fun β : StepField α Mark ↦ fun u : B ↦ β u.1) :=
      Measurable.of_comap_le le_rfl
    apply measurable_pi_iff.mpr
    intro p
    exact (measurable_pi_apply (⟨List.ofFn p.2, by simp [B]⟩ : B)).comp hrest
  exact indep_of_indep_of_le hi (fieldPrefix_measurable F hF s n).comap_le hB.comap_le

private lemma generationBroods_law {α Mark : Type*} [MeasurableSpace Mark]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ] (n : ℕ) :
    (offspringFieldLaw μ).map
      (fun β (p : Unit × (Fin n → α)) ↦ β (List.ofFn p.2)) =
      Measure.infinitePi (fun _ : Unit × (Fin n → α) ↦ μ) := by
  apply Measure.map_infinitePi_infinitePi_of_inj
  rintro ⟨r, u⟩ ⟨q, v⟩ h
  have huv : u = v := List.ofFn_injective h
  subst v
  cases r
  cases q
  rfl

private lemma fieldStatePath_child {α Mark S : Type*} (F : S → Mark → S) (s : S)
    (β : StepField α Mark) (n : ℕ) (p : Unit × (Fin (n + 1) → α)) :
    fieldStatePath F s β (n + 1) p =
      updateBrood F (fieldStatePath F s β n (p.1, Fin.init p.2))
        (β (List.ofFn (Fin.init p.2))) (p.2 (Fin.last n)) := by
  have he : List.ofFn p.2 =
      List.ofFn (Fin.init p.2) ++ [p.2 (Fin.last n)] := by
    simpa only [List.concat_eq_append, Fin.init_def] using List.ofFn_succ' p.2
  change stateTree F s β (List.ofFn p.2) = _
  rw [he, stateTree_append_singleton]
  change (stateTree F s β (List.ofFn (Fin.init p.2))).bind _ =
    updateBrood F (stateTree F s β (List.ofFn (Fin.init p.2))) _ _
  cases stateTree F s β (List.ofFn (Fin.init p.2)) <;> rfl

private lemma fieldStatePath_law {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (s : S) :
    (offspringFieldLaw μ).map (fieldStatePath F s) =
      pathKernel (offspringStateKernel F hF (Kernel.const S μ)) (some s) := by
  let P := offspringFieldLaw μ
  let K := offspringStateKernel F hF (Kernel.const S μ)
  have hX := fieldStatePath_measurable (α := α) F hF s
  rw [pathKernel_eq_generationPathLaw, generationPathLaw,
    Measure.map_dirac' (by fun_prop)]
  apply Kernel.eq_trajMeasure
  · rw [Measure.map_map (measurable_pi_apply 0) hX]
    have he : (fun β : StepField α Mark ↦ fieldStatePath F s β 0) =
        (fun _ ↦ fun _ : Unit × (Fin 0 → α) ↦ some s) := by
      funext β p
      simp [fieldStatePath]
    rw [show ((fun x ↦ x 0) ∘ fieldStatePath F s) =
      (fun β ↦ fieldStatePath F s β 0) from rfl, he]
    simp
  · intro n
    let A := fun β : StepField α Mark ↦ frestrictLe n (fieldStatePath F s β)
    let B := fun (β : StepField α Mark) (p : Unit × (Fin n → α)) ↦ β (List.ofFn p.2)
    let ν := Measure.infinitePi (fun _ : Unit × (Fin n → α) ↦ μ)
    let D (p : (Π k : Iic n, (Unit × (Fin k.1 → α)) → Option S) ×
        ((Unit × (Fin n → α)) → Step α Mark)) (q : Unit × (Fin (n + 1) → α)) :=
      updateBrood F (p.1 ⟨n, by simp⟩ (q.1, Fin.init q.2))
        (p.2 (q.1, Fin.init q.2)) (q.2 (Fin.last n))
    have hA : Measurable A := (measurable_frestrictLe n).comp hX
    have hB : Measurable B := by fun_prop
    have hD : Measurable D := by
      apply measurable_pi_iff.mpr
      intro q
      have hinputs : Measurable (fun p :
          (Π k : Iic n, (Unit × (Fin k.1 → α)) → Option S) ×
            ((Unit × (Fin n → α)) → Step α Mark) ↦
          (p.1 ⟨n, by simp⟩ (q.1, Fin.init q.2), p.2 (q.1, Fin.init q.2))) := by fun_prop
      exact (measurable_pi_apply (q.2 (Fin.last n))).comp
        ((updateBrood_measurable F hF).comp hinputs)
    have hpair : P.map (fun β ↦ (A β, B β)) = (P.map A).prod ν := by
      rw [(fieldPrefix_broods_independent μ F hF s n).map_prod_eq_prod_map_map
        hA.aemeasurable hB.aemeasurable, generationBroods_law]
    have hlift : ((P.map A).prod ν).map (fun p ↦ (p.1, D p)) =
        (P.map A) ⊗ₘ generationHistoryKernel K n := by
      ext E hE
      rw [Measure.map_apply (measurable_fst.prodMk hD) hE,
        Measure.prod_apply (hE.preimage (measurable_fst.prodMk hD)),
        Measure.compProd_apply hE]
      apply lintegral_congr_ae
      filter_upwards [] with h
      change ν ((fun b ↦ (h, D (h, b))) ⁻¹' E) =
        generationKernel K n (h ⟨n, by simp⟩) (Prod.mk h ⁻¹' E)
      rw [← updateGeneration_law μ F hF n (h ⟨n, by simp⟩)]
      exact (Measure.map_apply
        (hD.comp (measurable_const.prodMk measurable_id))
        (measurable_prodMk_left hE)).symm
    have hp := congrArg (fun m ↦ m.map (fun p ↦ (p.1, D p))) hpair
    rw [Measure.map_map (measurable_fst.prodMk hD) (hA.prodMk hB), hlift] at hp
    have he : (fun β ↦ (A β, D (A β, B β))) =
        (fun β ↦ (frestrictLe n (fieldStatePath F s β), fieldStatePath F s β (n + 1))) := by
      funext β
      apply Prod.ext
      · rfl
      funext q
      exact (fieldStatePath_child F s β n q).symm
    change P.map (fun β ↦ (A β, D (A β, B β))) = _ at hp
    rw [he] at hp
    rw [Measure.map_map (measurable_frestrictLe n) hX,
      Measure.map_map (by fun_prop) hX]
    exact hp.symm

/-- The independent offspring field realizes the unique canonical state-tree
law for the constant mark kernel, for every jointly measurable update. -/
theorem map_stateTree_offspringFieldLaw {α Mark S : Type*}
    [MeasurableSpace Mark] [MeasurableSpace S]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (F : S → Mark → S) (hF : Measurable (Function.uncurry F)) (s : S) :
    (offspringFieldLaw μ).map (stateTree F s) =
      treeKernel (offspringStateKernel F hF (Kernel.const S μ)) (some s) := by
  have h := congrArg (fun m ↦ m.map
    (fun x (u : List α) ↦ x u.length ((), u.get))) (fieldStatePath_law μ F hF s)
  rw [Measure.map_map (by fun_prop) (fieldStatePath_measurable F hF s)] at h
  simp only [Function.comp_def, fieldStatePath, List.ofFn_get] at h
  rw [treeKernel, Kernel.map_apply _ (by fun_prop)]
  exact h

end ProbabilityTheory.BranchingProcess.State
