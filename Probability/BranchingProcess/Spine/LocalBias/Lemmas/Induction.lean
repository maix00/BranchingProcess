/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingProcess.Spine.LocalBias.Weight
import Probability.BranchingProcess.Spine.Tree.Observation.Path
import all Probability.BranchingProcess.Spine.LocalBias.Lemmas.Generation

/-!
# Fixed-address finite-history induction

## Internal proof declarations

* `lintegral_partialTraj_fixedAddress` proves
  `E_spine[1_{wₙ=z} g(erase(Hₙ))] = E[W_z(Hₙ) g(Hₙ)]`
  by induction on `n` along the fixed address, for measurable `g ≥ 0`.

This is the fixed ancestral address induction of Zhan Shi, *Branching Random
Walks* (2015), §4.5, (4.12)–(4.13), DOI 10.1007/978-3-319-25372-5.
-/

open MeasureTheory ProbabilityTheory Combinatorics.Branching Finset Preorder
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias

private noncomputable def appendHistory {S ι : Type*} [MeasurableSpace S] (n : ℕ)
    (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S)
    (y : (Unit × (Fin (n + 1) → ι)) → Option S) :
    Π k : Iic (n + 1), (Unit × (Fin k.1 → ι)) → Option S :=
  IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S) n (n + 1)
    (x, MeasurableEquiv.piSingleton (X := fun k => (Unit × (Fin k → ι)) → Option S) n y)

private lemma measurable_appendHistory {S ι : Type*} [MeasurableSpace S]
    (n : ℕ) : Measurable (fun p :
      (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) ×
        ((Unit × (Fin (n + 1) → ι)) → Option S) => appendHistory n p.1 p.2) :=
  measurable_IicProdIoc.comp (measurable_fst.prodMk
    ((MeasurableEquiv.piSingleton (X := fun k => (Unit × (Fin k → ι)) → Option S) n).measurable.comp measurable_snd))

private lemma appendHistory_old {S ι : Type*} [MeasurableSpace S] (n : ℕ)
    (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S)
    (y : (Unit × (Fin (n + 1) → ι)) → Option S) (k : Iic n) :
    appendHistory n x y ⟨k.1, mem_Iic.mpr ((mem_Iic.mp k.2).trans n.le_succ)⟩ = x k := by
  simp [appendHistory, IicProdIoc_def, mem_Iic.mp k.2]

private lemma appendHistory_last {S ι : Type*} [MeasurableSpace S] (n : ℕ)
    (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S)
    (y : (Unit × (Fin (n + 1) → ι)) → Option S) :
    appendHistory n x y ⟨n + 1, by simp⟩ = y := by
  simp [appendHistory, IicProdIoc_def, MeasurableEquiv.piSingleton]

private lemma addressWeight_append {S ι : Type*} [MeasurableSpace S]
    (B : LocalBias S ι) (n : ℕ) (z : Fin (n + 1) → ι)
    (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S)
    (y : (Unit × (Fin (n + 1) → ι)) → Option S) :
    addressWeight B (n + 1) z (appendHistory n x y) =
      addressWeight B n (Fin.init z) x *
        stepWeight B (x ⟨n, by simp⟩ ((), Fin.init z))
          (fun j => y ((), Fin.snoc (Fin.init z) j)) (z (Fin.last n)) := by
  have hm : appendHistory n x y ⟨n, by simp⟩ = x ⟨n, by simp⟩ :=
    appendHistory_old n x y ⟨n, by simp⟩
  simp only [addressWeight, appendHistory_old, appendHistory_last, hm]

private lemma map_appendHistory {S T ι : Type*} [MeasurableSpace S] [MeasurableSpace T] (f : S → T) (n : ℕ)
    (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S)
    (y : (Unit × (Fin (n + 1) → ι)) → Option S) :
    (fun k q => (appendHistory n x y k q).map f) =
      appendHistory n (fun k q => (x k q).map f) (fun q => (y q).map f) := by
  funext k
  rcases k with ⟨k, hk⟩
  by_cases hkn : k ≤ n
  · funext q
    simp [appendHistory, IicProdIoc_def, hkn]
  · have he : k = n + 1 := by have := mem_Iic.mp hk; omega
    subst k
    simp only [appendHistory_last]

private lemma lintegral_appendHistory {S ι : Type*} [MeasurableSpace S]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q] (s : Option S) (n : ℕ)
    {g : (Π k : Iic (n + 1), (Unit × (Fin k.1 → ι)) → Option S) → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ x, g x ∂Kernel.partialTraj
      (X := fun k => (Unit × (Fin k → ι)) → Option S)
      (State.generationHistoryKernel Q) 0 (n + 1) (fun _ _ => s)) =
    ∫⁻ x, ∫⁻ y, g (appendHistory n x y) ∂State.generationHistoryKernel Q n x
      ∂Kernel.partialTraj (X := fun k => (Unit × (Fin k → ι)) → Option S)
        (State.generationHistoryKernel Q) 0 n (fun _ _ => s) := by
  rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n),
    Kernel.lintegral_map _ ((measurable_IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S))) _ hg]
  rw [Kernel.lintegral_comp _ _ _
    (g := fun p => g (IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S) n (n + 1) p)) (hg.comp (measurable_IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S)))]
  simp_rw [Kernel.lintegral_id_prod (f := fun p => g (IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S) n (n + 1) p))
    (hg.comp (measurable_IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S)))]
  apply lintegral_congr
  intro x
  exact Kernel.lintegral_map _ (MeasurableEquiv.piSingleton
    (X := fun k => (Unit × (Fin k → ι)) → Option S) n).measurable _
    (g' := fun y => g (IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S) n (n + 1) (x, y)))
    (hg.comp ((measurable_IicProdIoc (X := fun k => (Unit × (Fin k → ι)) → Option S)).comp (measurable_const.prodMk measurable_id)))

private lemma ae_pathKernel_unique_distinguished {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain) :
    letI := reproductionKernel_isMarkovKernel Q B hB
    ∀ᵐ x ∂State.pathKernel (reproductionKernel Q B) (some (Sum.inr s)),
      ∀ n, ∃! p : Unit × (Fin n → ι), (x n p).any Sum.isRight = true := by
  let := reproductionKernel_isMarkovKernel Q B hB
  have hG : MeasurableSet {x : Π n : ℕ,
      (Unit × (Fin n → ι)) → Option (S ⊕ B.domain) |
      ∀ n, ∃! p, (x n p).any Sum.isRight = true} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_unique_distinguished.preimage (measurable_pi_apply n)
  rw [← State.treeKernel_generations (reproductionKernel Q B) (some (Sum.inr s))]
  apply (ae_map_iff
    (show Measurable (fun t : List ι → Option (S ⊕ B.domain) =>
      fun n (p : Unit × (Fin n → ι)) => t (List.ofFn p.2)) from by fun_prop).aemeasurable hG).mpr
  filter_upwards [ae_treeKernel_unique_spine Q B hB s] with t ht
  obtain ⟨f, ⟨hf, hcarrier⟩, _⟩ := ht
  exact fun n => existsUnique_distinguished_generation t f hf hcarrier n


private lemma ae_partialTraj_unique {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain) (n : ℕ) :
    letI := reproductionKernel_isMarkovKernel Q B hB
    ∀ᵐ x ∂Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) →
        Option (S ⊕ B.domain))
      (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q B)) 0 n
      (fun _ _ => some (Sum.inr s)),
      ∃! p, (x ⟨n, by simp⟩ p).any Sum.isRight = true := by
  let := reproductionKernel_isMarkovKernel Q B hB
  have hm : (State.pathKernel (reproductionKernel Q B) (some (Sum.inr s))).map
      (frestrictLe n) = Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) →
        Option (S ⊕ B.domain))
      (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q B)) 0 n
          (fun _ _ => some (Sum.inr s)) := by
    exact Kernel.traj_map_frestrictLe_apply 0 n _
  rw [← hm]
  apply (ae_map_iff (measurable_frestrictLe n).aemeasurable
    (measurableSet_unique_distinguished.preimage (measurable_pi_apply _))).mpr
  exact (ae_pathKernel_unique_distinguished Q B hB s).mono (fun x hx => hx n)

lemma lintegral_partialTraj_fixedAddress {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain) (n : ℕ) (z : Fin n → ι)
    {g : (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) → ℝ≥0∞}
    (hg : Measurable g) :
    letI := reproductionKernel_isMarkovKernel Q B hB
    (∫⁻ x, if (x ⟨n, by simp⟩ ((), z)).any Sum.isRight = true then
      g (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0
      ∂Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) →
        Option (S ⊕ B.domain))
      (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q B)) 0 n (fun _ _ => some (Sum.inr s))) =
    ∫⁻ x, addressWeight B n z x * g x
      ∂Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) → Option S)
      (State.generationHistoryKernel (Root := Unit) Q) 0 n
        (fun _ _ => some s.1) := by
  let := reproductionKernel_isMarkovKernel Q B hB
  let E := S ⊕ B.domain
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false (measurable_const.sumElim measurable_const)
  have herase (n : ℕ) : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option E =>
      fun k q => (x k q).map (Sum.elim id Subtype.val)) := by
    have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
      measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
    fun_prop
  induction n with
  | zero =>
    have hL : Measurable (fun x : Π k : Iic 0,
        (Unit × (Fin k.1 → ι)) → Option E =>
        if (x ⟨0, by simp⟩ ((), z)).any Sum.isRight = true then
          g (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0) :=
      (hg.comp (herase 0)).ite ((MeasurableSet.singleton true).preimage
        (htag.comp ((measurable_pi_apply _).comp (measurable_pi_apply _)))) measurable_const
    rw [Kernel.partialTraj_self, Kernel.id_apply, lintegral_dirac' _ hL,
      Kernel.partialTraj_self, Kernel.id_apply,
      lintegral_dirac' _ (show Measurable (fun x : Π k : Iic 0,
        (Unit × (Fin k.1 → ι)) → Option S => addressWeight B 0 z x * g x) from
          (measurable_addressWeight B hB.measurableSet_domain hB.measurable_density 0 z).mul hg)]
    simp only [Option.any_some, Sum.isRight_inr, ite_true,
      Option.map_some, Sum.elim_inr, addressWeight, one_mul]
  | succ n ih =>
    let F (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) :=
      ∫⁻ y, stepWeight B (x ⟨n, by simp⟩ ((), Fin.init z))
        (fun j => y ((), Fin.snoc (Fin.init z) j)) (z (Fin.last n)) *
        g (appendHistory n x y) ∂State.generationHistoryKernel Q n x
    have hpay : Measurable (fun p :
        (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) ×
          ((Unit × (Fin (n + 1) → ι)) → Option S) =>
        stepWeight B (p.1 ⟨n, by simp⟩ ((), Fin.init z))
          (fun j => p.2 ((), Fin.snoc (Fin.init z) j)) (z (Fin.last n)) *
          g (appendHistory n p.1 p.2)) :=
      ((measurable_stepWeight B hB.measurableSet_domain hB.measurable_density _).comp
        (show Measurable (fun p :
            (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) ×
              ((Unit × (Fin (n + 1) → ι)) → Option S) =>
          (p.1 ⟨n, by simp⟩ ((), Fin.init z),
            fun j => p.2 ((), Fin.snoc (Fin.init z) j))) from by fun_prop)).mul
        (hg.comp (measurable_appendHistory n))
    have hF : Measurable F := hpay.lintegral_kernel_prod_right'
    have hL : Measurable (fun x : Π k : Iic (n + 1),
        (Unit × (Fin k.1 → ι)) → Option E =>
        if (x ⟨n + 1, by simp⟩ ((), z)).any Sum.isRight = true then
          g (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0) :=
      (hg.comp (herase (n + 1))).ite ((MeasurableSet.singleton true).preimage
        (htag.comp ((measurable_pi_apply _).comp (measurable_pi_apply _)))) measurable_const
    rw [lintegral_appendHistory (reproductionKernel Q B) (some (Sum.inr s)) n hL]
    calc
      _ = ∫⁻ x, (if (x ⟨n, by simp⟩ ((), Fin.init z)).any Sum.isRight = true then
          F (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0)
          ∂Kernel.partialTraj (X := fun k => (Unit × (Fin k → ι)) → Option E)
            (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q B)) 0 n
            (fun _ _ => some (Sum.inr s)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_partialTraj_unique Q B hB s n] with x hx
        have hgn : Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option S =>
            g (appendHistory n (fun k q => (x k q).map (Sum.elim id Subtype.val)) y)) :=
          hg.comp ((measurable_appendHistory n).comp (measurable_const.prodMk measurable_id))
        have hchildMeas : Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option E =>
            if (y ((), z)).any Sum.isRight = true then
              g (appendHistory n (fun k q => (x k q).map (Sum.elim id Subtype.val))
                (fun q => (y q).map (Sum.elim id Subtype.val))) else 0) :=
          (hgn.comp (by
            have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
              measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
            fun_prop)).ite ((MeasurableSet.singleton true).preimage
              (htag.comp (measurable_pi_apply _))) measurable_const
        change (∫⁻ y, if (appendHistory n x y ⟨n + 1, by simp⟩ ((), z)).any
            Sum.isRight = true then
              g (fun k q => (appendHistory n x y k q).map (Sum.elim id Subtype.val)) else 0
            ∂State.generationKernel (reproductionKernel Q B) n (x ⟨n, by simp⟩)) = _
        simp only [appendHistory_last, map_appendHistory]
        by_cases hp : (x ⟨n, by simp⟩ ((), Fin.init z)).any Sum.isRight = true
        · obtain ⟨a, ha⟩ : ∃ a,
              x ⟨n, by simp⟩ ((), Fin.init z) = some (Sum.inr a) := by
            cases he : x ⟨n, by simp⟩ ((), Fin.init z) with
            | none => simp [he] at hp
            | some a => cases a with
              | inl a => simp [he] at hp
              | inr a => exact ⟨a, rfl⟩
          have ho : ∀ q, q ≠ ((), Fin.init z) →
              (x ⟨n, by simp⟩ q).any Sum.isRight ≠ true := by
            obtain ⟨p, hpt, hu⟩ := hx
            intro q hq hqt
            exact hq ((hu q hqt).trans (hu _ hp).symm)
          have H := lintegral_generationKernel_fixedChild Q B hB n
            (x ⟨n, by simp⟩) ((), Fin.init z) a ha ho (z (Fin.last n)) hgn
          simp only [Fin.snoc_init_self] at H
          rw [H, ite_eq_left hp]
          simp only [F, ha, Option.map_some, Sum.elim_inr,
            stepWeight, Option.elim_some, a.2, ite_true]
          rfl
        · have hn := ae_generationKernel_normal_child Q B hB n
            (x ⟨n, by simp⟩) ((), Fin.init z) hp (z (Fin.last n))
          simp only [Fin.snoc_init_self] at hn
          rw [ite_eq_right hp]
          apply lintegral_eq_zero_of_ae_eq_zero
          filter_upwards [hn] with y hy
          exact ite_eq_right hy
      _ = ∫⁻ x, addressWeight B n (Fin.init z) x * F x
          ∂Kernel.partialTraj (X := fun k => (Unit × (Fin k → ι)) → Option S)
            (State.generationHistoryKernel (Root := Unit) Q) 0 n
            (fun _ _ => some s.1) := ih (Fin.init z) hF
      _ = _ := by
        rw [lintegral_appendHistory Q (some s.1) n
          (show Measurable (fun x : Π k : Iic (n + 1),
            (Unit × (Fin k.1 → ι)) → Option S => addressWeight B (n + 1) z x * g x) from
              (measurable_addressWeight B hB.measurableSet_domain hB.measurable_density (n + 1) z).mul hg)]
        apply lintegral_congr
        intro x
        simp only [addressWeight_append]
        dsimp only [F]
        have hpx : Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option S =>
            stepWeight B (x ⟨n, by simp⟩ ((), Fin.init z))
              (fun j => y ((), Fin.snoc (Fin.init z) j)) (z (Fin.last n)) *
              g (appendHistory n x y)) :=
          hpay.comp (measurable_const.prodMk measurable_id)
        rw [← lintegral_const_mul _ hpx]
        apply lintegral_congr
        intro y
        rw [mul_assoc]

end ProbabilityTheory.BranchingProcess.Spine.LocalBias
