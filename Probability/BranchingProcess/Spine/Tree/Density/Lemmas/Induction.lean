/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingProcess.Spine.Tree.Density.Weight
import all Probability.BranchingProcess.Spine.Tree.Density.Lemmas.Generation
import all Probability.BranchingProcess.Spine.Tree.Lemmas.PathLaw

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

namespace ProbabilityTheory.BranchingProcess.Spine

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

private lemma addressWeight_append {S ι : Type*} [MeasurableSpace S] (h : S → ℝ≥0∞) (n : ℕ)
    (z : Fin (n + 1) → ι)
    (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S)
    (y : (Unit × (Fin (n + 1) → ι)) → Option S) :
    addressWeight h (n + 1) z (appendHistory n x y) =
      addressWeight h n (Fin.init z) x *
        if (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ 0 ∧
            (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ ∞ then
          (y ((), z)).elim 0 h / (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h else 0 := by
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

private lemma ae_partialTraj_unique {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) :
    letI := reproductionKernel_isMarkovKernel Q hh harmonic
    ∀ᵐ x ∂Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) →
        Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
      (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q h)) 0 n
      (fun _ _ => some (Sum.inr s)),
      ∃! p, (x ⟨n, by simp⟩ p).any Sum.isRight = true := by
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  have hm : (State.pathKernel (reproductionKernel Q h) (some (Sum.inr s))).map
      (frestrictLe n) = Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) →
        Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
      (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q h)) 0 n
          (fun _ _ => some (Sum.inr s)) := by
    exact Kernel.traj_map_frestrictLe_apply 0 n _
  rw [← hm]
  apply (ae_map_iff (measurable_frestrictLe n).aemeasurable
    (measurableSet_unique_distinguished.preimage (measurable_pi_apply _))).mpr
  exact (ae_pathKernel_unique_distinguished Q hh harmonic s).mono (fun x hx => hx n)

lemma lintegral_partialTraj_fixedAddress {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) (z : Fin n → ι)
    {g : (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) → ℝ≥0∞}
    (hg : Measurable g) :
    letI := reproductionKernel_isMarkovKernel Q hh harmonic
    (∫⁻ x, if (x ⟨n, by simp⟩ ((), z)).any Sum.isRight = true then
      g (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0
      ∂Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) →
        Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
      (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q h)) 0 n (fun _ _ => some (Sum.inr s))) =
    ∫⁻ x, addressWeight h n z x * g x
      ∂Kernel.partialTraj (X := fun n => (Unit × (Fin n → ι)) → Option S)
      (State.generationHistoryKernel (Root := Unit) Q) 0 n
        (fun _ _ => some s.1) := by
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
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
        (Unit × (Fin k.1 → ι)) → Option S => addressWeight h 0 z x * g x) from
          (measurable_addressWeight hh 0 z).mul hg)]
    simp only [Option.any_some, Sum.isRight_inr, ite_true,
      Option.map_some, Sum.elim_inr, addressWeight, one_mul]
  | succ n ih =>
    let F (x : Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) :=
      if (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ 0 ∧
          (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ ∞ then
        ∫⁻ y, ((y ((), z)).elim 0 h /
          (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h) * g (appendHistory n x y)
          ∂State.generationHistoryKernel Q n x else 0
    have hden : Measurable (fun x : Π k : Iic n,
        (Unit × (Fin k.1 → ι)) → Option S =>
        (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h) :=
      (measurable_option_elim 0 hh).comp
        ((measurable_pi_apply _).comp (measurable_pi_apply _))
    have hpay : Measurable (fun p :
        (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) ×
          ((Unit × (Fin (n + 1) → ι)) → Option S) =>
        ((p.2 ((), z)).elim 0 h /
          (p.1 ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h) *
          g (appendHistory n p.1 p.2)) :=
      (((measurable_option_elim 0 hh).comp
        ((measurable_pi_apply _).comp measurable_snd)).div
          (hden.comp measurable_fst)).mul (hg.comp (measurable_appendHistory n))
    have hF : Measurable F := hpay.lintegral_kernel_prod_right'.ite
      ((hden (MeasurableSet.singleton 0).compl).inter
        (hden (MeasurableSet.singleton ∞).compl)) measurable_const
    have hL : Measurable (fun x : Π k : Iic (n + 1),
        (Unit × (Fin k.1 → ι)) → Option E =>
        if (x ⟨n + 1, by simp⟩ ((), z)).any Sum.isRight = true then
          g (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0) :=
      (hg.comp (herase (n + 1))).ite ((MeasurableSet.singleton true).preimage
        (htag.comp ((measurable_pi_apply _).comp (measurable_pi_apply _)))) measurable_const
    rw [lintegral_appendHistory (reproductionKernel Q h) (some (Sum.inr s)) n hL]
    calc
      _ = ∫⁻ x, (if (x ⟨n, by simp⟩ ((), Fin.init z)).any Sum.isRight = true then
          F (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0)
          ∂Kernel.partialTraj (X := fun k => (Unit × (Fin k → ι)) → Option E)
            (State.generationHistoryKernel (Root := Unit) (reproductionKernel Q h)) 0 n
            (fun _ _ => some (Sum.inr s)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_partialTraj_unique Q hh harmonic s n] with x hx
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
            ∂State.generationKernel (reproductionKernel Q h) n (x ⟨n, by simp⟩)) = _
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
          have H := lintegral_generationKernel_fixedChild Q hh harmonic n
            (x ⟨n, by simp⟩) ((), Fin.init z) a ha ho (z (Fin.last n)) hgn
          simp only [Fin.snoc_init_self] at H
          rw [H, ite_eq_left hp]
          simp only [F, ha, Option.map_some, Sum.elim_inr, Option.elim_some,
            ne_eq, a.2.1, a.2.2, not_false_eq_true, and_self, ite_true]
          rfl
        · have hn := ae_generationKernel_normal_child Q hh harmonic n
            (x ⟨n, by simp⟩) ((), Fin.init z) hp (z (Fin.last n))
          simp only [Fin.snoc_init_self] at hn
          rw [ite_eq_right hp]
          apply lintegral_eq_zero_of_ae_eq_zero
          filter_upwards [hn] with y hy
          exact ite_eq_right hy
      _ = ∫⁻ x, addressWeight h n (Fin.init z) x * F x
          ∂Kernel.partialTraj (X := fun k => (Unit × (Fin k → ι)) → Option S)
            (State.generationHistoryKernel (Root := Unit) Q) 0 n
            (fun _ _ => some s.1) := ih (Fin.init z) hF
      _ = _ := by
        rw [lintegral_appendHistory Q (some s.1) n
          (show Measurable (fun x : Π k : Iic (n + 1),
            (Unit × (Fin k.1 → ι)) → Option S => addressWeight h (n + 1) z x * g x) from
              (measurable_addressWeight hh (n + 1) z).mul hg)]
        apply lintegral_congr
        intro x
        simp only [addressWeight_append]
        by_cases hx : (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ 0 ∧
            (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h ≠ ∞
        · simp only [F, ite_eq_left hx]
          have hpx : Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option S =>
              ((y ((), z)).elim 0 h / (x ⟨n, by simp⟩ ((), Fin.init z)).elim 0 h) *
                g (appendHistory n x y)) :=
            hpay.comp (measurable_const.prodMk measurable_id)
          rw [← lintegral_const_mul _ hpx]
          apply lintegral_congr
          intro y
          rw [mul_assoc]
        · simp only [F, ite_eq_right hx, mul_zero, zero_mul, lintegral_zero]

end ProbabilityTheory.BranchingProcess.Spine
