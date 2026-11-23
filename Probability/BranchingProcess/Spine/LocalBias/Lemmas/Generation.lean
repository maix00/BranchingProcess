/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingProcess.Spine.LocalBias.Ray
import Probability.BranchingProcess.Spine.LocalBias.Weight
import Probability.BranchingProcess.State.Generation

/-!
# Single-parent integration for the fixed-address induction

## Internal proof declarations

* `lintegral_generationKernel_fixedChild` integrates one fixed distinguished
  child in the full next generation: its density is the local `r(parent,family,index)`;
  all other parents reproduce with the original law.
* `ae_generationKernel_normal_child` proves that a fixed child of a normal
  or absent parent has no distinguished tag, almost surely.

The proof follows Zhan Shi, *Branching Random Walks* (2015), §4.5,
proof of Theorem 4.3, (4.12)–(4.13), DOI 10.1007/978-3-319-25372-5.
Independent ordinary parent families are integrated under their original
laws; the fixed distinguished parent's family contributes its child weight.
-/

open MeasureTheory ProbabilityTheory Combinatorics.Branching
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

namespace ProbabilityTheory.BranchingProcess.Spine.LocalBias

private noncomputable def joinAt {J X : Type*} (p : J) (a : X) (b : {j // j ≠ p} → X) : J → X := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun j : J => j = p) (fun _ => X)).symm
    (fun _ => a, b)

private lemma measurable_joinAt {J X : Type*} [MeasurableSpace X] (p : J) :
    Measurable (fun q : X × ({j // j ≠ p} → X) => joinAt p q.1 q.2) := by
  classical
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => X) (fun j => j = p)).symm.measurable.comp
    ((show Measurable (fun q : X × ({j // j ≠ p} → X) =>
      fun _j : {j : J // j = p} => q.1) from by fun_prop).prodMk measurable_snd)

private lemma infinitePi_split {J X : Type*} [MeasurableSpace X]
    (μ : J → Measure X) [∀ j, IsProbabilityMeasure (μ j)] (p : J) :
    Measure.infinitePi μ = ((μ p).prod
      (Measure.infinitePi (fun j : {j // j ≠ p} => μ j))).map
        (fun q => joinAt p q.1 q.2) := by
  classical
  let split (x : J → X) := (x p, fun j : {j // j ≠ p} => x j)
  have hi := (iIndepFun_infinitePi (P := μ) (X := fun _ x => x)
    (fun _ => measurable_id)).indepFun_set {p} {j | j ≠ p}
      (by simp) (fun j => measurable_pi_apply j)
  have hs : (Measure.infinitePi μ).map split =
      (μ p).prod (Measure.infinitePi (fun j : {j // j ≠ p} => μ j)) := by
    have h := hi.comp (measurable_pi_apply ⟨p, rfl⟩) measurable_id
    change (Measure.infinitePi μ).map (fun x : J → X => (x p, fun j : {j // j ≠ p} => x j)) = _
    rw [IndepFun.map_prod_eq_prod_map_map
      (measurable_pi_apply p).aemeasurable
      (show Measurable (fun x : J → X => fun j : {j // j ≠ p} => x j) from
        by fun_prop).aemeasurable]
    · rw [Measure.infinitePi_map_eval,
        Measure.map_infinitePi_infinitePi_of_inj (P := μ) Subtype.val_injective]
    · exact h
  rw [← hs, Measure.map_map (measurable_joinAt p) (by fun_prop)]
  have he : (fun x : J → X => joinAt p (x p) (fun j => x j)) = id := by
    funext x j
    by_cases hj : j = p <;> simp [joinAt, Equiv.piEquivPiSubtypeProd_symm_apply, hj]
  change _ = (Measure.infinitePi μ).map (fun x => joinAt p (x p) (fun j => x j))
  rw [he, Measure.map_id]

private lemma lintegral_infinitePi_transfer {J X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : J → Measure X) (ν : J → Measure Y)
    [∀ j, IsProbabilityMeasure (μ j)] [∀ j, IsProbabilityMeasure (ν j)]
    (p : J) (f : X → Y) (hf : Measurable f)
    (r : X → ℝ≥0∞) (hr : Measurable r) (w : Y → ℝ≥0∞) (hw : Measurable w)
    (hother : ∀ j, j ≠ p → (μ j).map f = ν j)
    (hfixed : ∀ g : Y → ℝ≥0∞, Measurable g →
      (∫⁻ a, r a * g (f a) ∂μ p) = ∫⁻ b, w b * g b ∂ν p)
    {g : (J → Y) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x, r (x p) * g (fun j => f (x j)) ∂Measure.infinitePi μ) =
      ∫⁻ y, w (y p) * g y ∂Measure.infinitePi ν := by
  classical
  have hm : Measurable (fun x : J → X => r (x p) * g (fun j => f (x j))) :=
    (hr.comp (measurable_pi_apply p)).mul (hg.comp (by fun_prop))
  have hn : Measurable (fun x : J → Y => w (x p) * g x) :=
    (hw.comp (measurable_pi_apply p)).mul hg
  let H (b : {j // j ≠ p} → Y) := ∫⁻ a, w a * g (joinAt p a b) ∂ν p
  have hH : Measurable H := by
    exact (hw.comp measurable_fst |>.mul (hg.comp (measurable_joinAt p))).lintegral_prod_left'
  have hrest : (Measure.infinitePi (fun j : {j // j ≠ p} => μ j)).map
      (fun x j => f (x j)) = Measure.infinitePi (fun j : {j // j ≠ p} => ν j) := by
    rw [Measure.infinitePi_map_pi _ (fun _ => hf)]
    congr 1
    funext j
    exact hother j j.2
  have hjoin (a : X) (b : {j // j ≠ p} → X) :
      (fun j => f (joinAt p a b j)) = joinAt p (f a) (fun j => f (b j)) := by
    funext j
    by_cases hj : j = p <;> simp [joinAt, Equiv.piEquivPiSubtypeProd_symm_apply, hj]
  calc
    _ = ∫⁻ b, ∫⁻ a, r a * g (joinAt p (f a) (fun j => f (b j))) ∂μ p
        ∂Measure.infinitePi (fun j : {j // j ≠ p} => μ j) := by
      rw [infinitePi_split μ p, lintegral_map hm (measurable_joinAt p)]
      have hm' : Measurable (fun q : X × ({j // j ≠ p} → X) =>
          r (joinAt p q.1 q.2 p) * g (fun j => f (joinAt p q.1 q.2 j))) :=
        hm.comp (measurable_joinAt p)
      rw [lintegral_prod_symm _ hm'.aemeasurable]
      apply lintegral_congr
      intro b
      apply lintegral_congr
      intro a
      rw [hjoin]
      simp [joinAt, Equiv.piEquivPiSubtypeProd_symm_apply]
    _ = ∫⁻ b, H (fun j => f (b j))
        ∂Measure.infinitePi (fun j : {j // j ≠ p} => μ j) := by
      apply lintegral_congr
      intro b
      dsimp only [H]
      apply hfixed (fun a => g (joinAt p a (fun j => f (b j))))
      apply hg.comp
      simpa only [Function.comp_def] using (measurable_joinAt p).comp
        (show Measurable (fun a : Y => (a, fun j : {j // j ≠ p} => f (b j))) from
          measurable_id.prodMk measurable_const)
    _ = ∫⁻ b, H b ∂Measure.infinitePi (fun j : {j // j ≠ p} => ν j) := by
      rw [← hrest, lintegral_map hH (by fun_prop)]
    _ = _ := by
      rw [infinitePi_split ν p, lintegral_map hn (measurable_joinAt p)]
      have hn' : Measurable (fun q : Y × ({j // j ≠ p} → Y) =>
          w (joinAt p q.1 q.2 p) * g (joinAt p q.1 q.2)) := hn.comp (measurable_joinAt p)
      rw [lintegral_prod_symm _ hn'.aemeasurable]
      apply lintegral_congr
      intro b
      apply lintegral_congr
      intro a
      simp [joinAt, Equiv.piEquivPiSubtypeProd_symm_apply]

private lemma lintegral_reproduction_fixedChild {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q) (s : B.domain) (i : ι)
    {g : Step ι S → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ ξ, (if (ξ i).any Sum.isRight = true then (1 : ℝ≥0∞) else 0) *
      g (Step.map (Sum.elim id Subtype.val) ξ) ∂reproductionKernel Q B (Sum.inr s)) =
      ∫⁻ ξ, B.density s ξ i * g ξ ∂Q s := by
  classical
  let E := S ⊕ B.domain
  let G (ξ : Step ι E) := if (ξ i).any Sum.isRight = true then
    g (Step.map (Sum.elim id Subtype.val) ξ) else 0
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false (measurable_const.sumElim measurable_const)
  have hG : Measurable G :=
    (hg.comp (Step.map_measurable
      (measurable_id.sumElim measurable_subtype_coe))).ite
      ((MeasurableSet.singleton true).preimage (htag.comp (measurable_pi_apply i)))
      measurable_const
  have hindex : Measurable (fun p : Step ι S × ι => if p.2 = i then g p.1 else 0) :=
    (hg.comp measurable_fst).ite
      ((MeasurableSet.singleton i).preimage measurable_snd) measurable_const
  calc
    _ = ∫⁻ ξ, G ξ ∂reproductionKernel Q B (Sum.inr s) := by
      simp only [G, ite_mul, one_mul, zero_mul]
    _ = ∫⁻ p, G (Step.distinguishChild B.domain.Mem p.1 p.2)
        ∂familyChildKernel Q B s := by
      rw [reproductionKernel_distinguished Q B hB.measurableSet_domain]
      have hm : Measurable (fun p : Step ι S × ι =>
          Step.distinguishChild B.domain.Mem p.1 p.2) :=
        Step.distinguishChild_measurable hB.measurableSet_domain
      exact lintegral_map hG hm
    _ = ∫⁻ p, (if p.2 = i then g p.1 else 0) ∂familyChildKernel Q B s := by
      apply lintegral_congr_ae
      filter_upwards [ae_familyChildKernel_eligible Q B hB s.1 s.2] with p hp
      obtain ⟨t, ht, htD⟩ := hp
      dsimp only [G]
      have he : Step.map (Sum.elim id Subtype.val)
          (Step.distinguishChild B.domain.Mem p.1 p.2) = p.1 :=
        Step.distinguishChild_map B.domain.Mem p.1 p.2
      erw [he]
      by_cases hi : p.2 = i
      · rw [← hi]
        erw [Step.distinguishChild_selected B.domain.Mem p.1 p.2 ht htD]
        simp
      · erw [Step.distinguishChild_other B.domain.Mem p.1 p.2 i (Ne.symm hi)]
        cases p.1 i <;> simp [hi]
    _ = _ := by
      rw [lintegral_familyChildKernel Q B hB.measurable_density hindex]
      rw [tsum_eq_single i]
      · simp
      · intro j hji
        simp [hji]

lemma lintegral_generationKernel_fixedChild {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (n : ℕ)
    (x : (Unit × (Fin n → ι)) → Option (S ⊕ B.domain))
    (p : Unit × (Fin n → ι)) (s : B.domain)
    (hp : x p = some (Sum.inr s))
    (ho : ∀ q, q ≠ p → (x q).any Sum.isRight ≠ true) (i : ι)
    {g : ((Unit × (Fin (n + 1) → ι)) → Option S) → ℝ≥0∞} (hg : Measurable g) :
    letI := reproductionKernel_isMarkovKernel Q B hB
    (∫⁻ y, if (y (p.1, Fin.snoc p.2 i)).any Sum.isRight = true then
      g (fun q => (y q).map (Sum.elim id Subtype.val)) else 0
      ∂State.generationKernel (reproductionKernel Q B) n x) =
    ∫⁻ y, (B.density s (fun j => y (p.1, Fin.snoc p.2 j)) i) * g y
      ∂State.generationKernel Q n (fun q => (x q).map (Sum.elim id Subtype.val)) := by
  let := reproductionKernel_isMarkovKernel Q B hB
  let E := S ⊕ B.domain
  let μ (q : Unit × (Fin n → ι)) :=
    Kernel.optionElim (Measure.dirac (fun _ : ι => (none : Option E)))
      (reproductionKernel Q B) (x q)
  let ν (q : Unit × (Fin n → ι)) :=
    Kernel.optionElim (Measure.dirac (fun _ : ι => (none : Option S))) Q
      ((x q).map (Sum.elim id Subtype.val))
  let f : Step ι E → Step ι S := Step.map (Sum.elim id Subtype.val)
  have hf : Measurable f := Step.map_measurable
    (measurable_id.sumElim measurable_subtype_coe)
  let r (ξ : Step ι E) : ℝ≥0∞ := if (ξ i).any Sum.isRight = true then 1 else 0
  have hr : Measurable r := measurable_const.ite
    ((MeasurableSet.singleton true).preimage
      ((show Measurable (fun o : Option E => o.any Sum.isRight) from
        measurable_option_elim false (measurable_const.sumElim measurable_const)).comp
          (measurable_pi_apply i))) measurable_const
  have hw : Measurable (fun ξ : Step ι S => B.density s ξ i) :=
    (hB.measurable_density i).comp (measurable_const.prodMk measurable_id)
  have hother : ∀ q, q ≠ p → (μ q).map f = ν q := by
    intro q hqp
    have hq := ho q hqp
    cases he : x q with
    | none =>
      simp only [μ, ν, he, Option.map_none, Kernel.optionElim_none]
      rw [Measure.map_dirac' hf]
      rfl
    | some a =>
      cases a with
      | inr a => simp [he] at hq
      | inl a =>
        simp only [μ, ν, he, Option.map_some, Kernel.optionElim_some,
          Sum.elim_inl, id_eq]
        rw [reproductionKernel_normal Q B a]
        rw [Measure.map_map hf (Step.map_measurable measurable_inl)]
        have hcomp : (f ∘ Step.map (Sum.inl : S → E)) = id := by
          funext ξ j
          cases heξ : ξ j <;> simp [f, Step.map, heξ]
        rw [hcomp, Measure.map_id]
  have hfixed : ∀ G : Step ι S → ℝ≥0∞, Measurable G →
      (∫⁻ a, r a * G (f a) ∂μ p) = ∫⁻ b, (B.density s b i) * G b ∂ν p := by
    intro G hG
    simpa only [μ, ν, hp, Option.map_some, Sum.elim_inr, Kernel.optionElim_some]
      using lintegral_reproduction_fixedChild Q B hB s i hG
  let G (broods : (Unit × (Fin n → ι)) → Step ι S) :=
    g (fun q => broods (q.1, Fin.init q.2) (q.2 (Fin.last n)))
  have hG : Measurable G := hg.comp (by fun_prop)
  have ht := lintegral_infinitePi_transfer μ ν p f hf r hr _ hw hother hfixed hG
  have hleft : Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option E =>
      if (y (p.1, Fin.snoc p.2 i)).any Sum.isRight = true then
        g (fun q => (y q).map (Sum.elim id Subtype.val)) else 0) := by
    have he : Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option E =>
        fun q => (y q).map (Sum.elim id Subtype.val)) := by
      have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
        measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
      fun_prop
    exact (hg.comp he).ite ((MeasurableSet.singleton true).preimage
      ((show Measurable (fun o : Option E => o.any Sum.isRight) from
        measurable_option_elim false (measurable_const.sumElim measurable_const)).comp
          (measurable_pi_apply _))) measurable_const
  have hright : Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option S =>
      B.density s (fun j => y (p.1, Fin.snoc p.2 j)) i * g y) :=
    ((hB.measurable_density i).comp (measurable_const.prodMk (by fun_prop))).mul hg
  rw [State.generationKernel_apply, lintegral_map hleft (by fun_prop),
    State.generationKernel_apply, lintegral_map hright (by fun_prop)]
  simpa only [Fin.init_snoc, Fin.snoc_last, r, G, f, Step.map,
    ite_mul, one_mul, zero_mul] using ht

lemma ae_generationKernel_normal_child {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : LocalBias S ι) (hB : B.IsAdmissible Q)
    (n : ℕ)
    (x : (Unit × (Fin n → ι)) → Option (S ⊕ B.domain))
    (p : Unit × (Fin n → ι)) (hn : (x p).any Sum.isRight ≠ true) (i : ι) :
    letI := reproductionKernel_isMarkovKernel Q B hB
    ∀ᵐ y ∂State.generationKernel (reproductionKernel Q B) n x,
      (y (p.1, Fin.snoc p.2 i)).any Sum.isRight ≠ true := by
  let := reproductionKernel_isMarkovKernel Q B hB
  let E := S ⊕ B.domain
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false (measurable_const.sumElim measurable_const)
  have hA : MeasurableSet {ξ : Step ι E | (ξ i).any Sum.isRight ≠ true} :=
    ((MeasurableSet.singleton true).preimage (htag.comp (measurable_pi_apply i))).compl
  have hm := State.generationKernel_childFamily (reproductionKernel Q B) n x p
  have hfamily : ∀ᵐ ξ ∂(State.generationKernel (reproductionKernel Q B) n x).map
      (fun y => fun j => y (p.1, Fin.snoc p.2 j)), (ξ i).any Sum.isRight ≠ true := by
    rw [hm]
    cases he : x p with
    | none =>
      rw [Kernel.optionElim_none]
      exact (ae_dirac_iff hA).mpr (by simp)
    | some a =>
      rw [Kernel.optionElim_some]
      cases a with
      | inr a => simp [he] at hn
      | inl a =>
        rw [reproductionKernel_normal]
        apply (ae_map_iff (Step.map_measurable measurable_inl).aemeasurable hA).mpr
        apply ae_of_all
        intro ξ
        cases heξ : ξ i <;> simp [Step.map, heξ]
  exact ae_of_ae_map (show Measurable (fun y : (Unit × (Fin (n + 1) → ι)) → Option E =>
    fun j => y (p.1, Fin.snoc p.2 j)) from by fun_prop).aemeasurable hfamily

end ProbabilityTheory.BranchingProcess.Spine.LocalBias
