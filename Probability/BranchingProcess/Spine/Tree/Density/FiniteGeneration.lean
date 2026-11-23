/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Density.Weight
public import Probability.BranchingProcess.Spine.Tree.Observation
import all Probability.BranchingProcess.Spine.Tree.Density.Lemmas.Induction

/-!
# Fixed-address densities on the canonical distinguished tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `lintegral_treeKernel_fixedAddress` proves, at every depth `n` and fixed
  address `z`, `E_spine[1_{wₙ=z} g(Hₙ)] = E[W_z(Hₙ) g(Hₙ)]` for every
  nonnegative measurable finite-history payoff. `W_z` is `addressWeight`.
* `treeKernel_finiteHistory` identifies the untyped finite-tree law as
  `P(Hₙ∈dx) (∑_z W_z(x))`, for all `n`.
* `treeKernel_fixedAddress_measure` gives the joint fixed-address law
  `P_spine(Hₙ∈dx,wₙ=z) = P(Hₙ∈dx) W_z(x)`.
* `lintegral_totalWeight` proves `E[∑_z W_z(Hₙ)] = 1`.
* `eq_treeKernel_marginal_of_finiteHistory` identifies the complete untyped
  tree law with any probability law having these finite-generation densities.
  It uses native projective-limit uniqueness, without a global density at infinity.

The proof is Zhan Shi, *Branching Random Walks* (2015), §4.5,
Theorem 4.3, (4.12)–(4.13), DOI 10.1007/978-3-319-25372-5.
It fixes the address before induction, integrates ordinary parent families
under their original laws, and multiplies the selected child's bias.
Both sides are observations of the existing canonical complete trees.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching Finset Preorder
open scoped ENNReal

private lemma treeKernel_history {S ι : Type*} [MeasurableSpace S]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q] (s : Option S) (n : ℕ) :
    (State.treeKernel Q s).map (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) =>
      t (List.ofFn p.2)) =
    Kernel.partialTraj (X := fun k => (Unit × (Fin k → ι)) → Option S)
      (State.generationHistoryKernel Q) 0 n (fun _ _ => s) := by
  change (State.treeKernel Q s).map ((frestrictLe n) ∘
    (fun t k (p : Unit × (Fin k → ι)) => t (List.ofFn p.2))) = _
  have hπ : Measurable (fun t : List ι → Option S =>
      fun k : ℕ => fun p : Unit × (Fin k → ι) => t (List.ofFn p.2)) := by fun_prop
  have hm := Measure.map_map (measurable_frestrictLe n) hπ (μ := State.treeKernel Q s)
  rw [State.treeKernel_generations] at hm
  exact hm.symm.trans (Kernel.traj_map_frestrictLe_apply 0 n _)

/-- Shi (4.12)–(4.13): the fixed-address identity at arbitrary depth,
for arbitrary nonnegative measurable observations through that generation. -/
theorem lintegral_treeKernel_fixedAddress {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) (z : Fin n → ι)
    {g : (Π k : Iic n, (Unit × (Fin k.1 → ι)) → Option S) → ℝ≥0∞}
    (hg : Measurable g) :
    (∫⁻ t, if (t (List.ofFn z)).any Sum.isRight = true then
      g (fun _k p => (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) else 0
      ∂treeKernel Q hh harmonic (some (Sum.inr s))) =
    ∫⁻ t, addressWeight h n z (fun _k p => t (List.ofFn p.2)) *
      g (fun _k p => t (List.ofFn p.2)) ∂State.treeKernel Q (some s.1) := by
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  have he : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option E =>
      fun k q => (x k q).map (Sum.elim id Subtype.val)) := by
    have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
      measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
    fun_prop
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false (measurable_const.sumElim measurable_const)
  have hG : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option E =>
      if (x ⟨n, by simp⟩ ((), z)).any Sum.isRight = true then
        g (fun k q => (x k q).map (Sum.elim id Subtype.val)) else 0) :=
    (hg.comp he).ite ((MeasurableSet.singleton true).preimage
      (htag.comp ((measurable_pi_apply _).comp (measurable_pi_apply _)))) measurable_const
  have hW : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option S => addressWeight h n z x * g x) :=
    (measurable_addressWeight hh n z).mul hg
  have hleft := lintegral_map hG (show Measurable
    (fun t : List ι → Option E => fun k : Iic n =>
      fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) from by fun_prop)
    (μ := State.treeKernel (reproductionKernel Q h) (some (Sum.inr s)))
  rw [treeKernel_history] at hleft
  have hright := lintegral_map hW (show Measurable
    (fun t : List ι → Option S => fun k : Iic n =>
      fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) from by fun_prop)
    (μ := State.treeKernel Q (some s.1))
  rw [treeKernel_history] at hright
  exact hleft.symm.trans ((lintegral_partialTraj_fixedAddress Q hh harmonic s n z hg).trans hright)

/-- Shi Theorem 4.3, (4.11): sum the fixed-address densities after their induction. -/
theorem treeKernel_finiteHistory {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) :
    (treeKernel Q hh harmonic (some (Sum.inr s))).map
      (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) =>
        (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) =
    ((State.treeKernel Q (some s.1)).map
      (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) => t (List.ofFn p.2))).withDensity
        (totalWeight h n) := by
  classical
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  have he : Measurable (fun t : List ι → Option E =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) =>
        (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) := by
    have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
      measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
    fun_prop
  have ht : Measurable (fun t : List ι → Option S =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) := by fun_prop
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false (measurable_const.sumElim measurable_const)
  apply Measure.ext_of_lintegral
  intro g hg
  have hWg : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option S => totalWeight h n x * g x) :=
    (measurable_totalWeight hh n).mul hg
  rw [lintegral_map hg he, lintegral_withDensity_eq_lintegral_mul _
    (measurable_totalWeight hh n) hg]
  simp only [Pi.mul_apply]
  rw [lintegral_map hWg ht]
  have hG (z : Fin n → ι) : Measurable (fun t : List ι → Option E =>
      if (t (List.ofFn z)).any Sum.isRight = true then
        g (fun k p => (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) else 0) :=
    (hg.comp he).ite ((MeasurableSet.singleton true).preimage
      (htag.comp (measurable_pi_apply _))) measurable_const
  calc
    _ = ∫⁻ t, ∑' z : Fin n → ι,
        (if (t (List.ofFn z)).any Sum.isRight = true then
          g (fun k p => (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) else 0)
        ∂treeKernel Q hh harmonic (some (Sum.inr s)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_treeKernel_unique_spine Q hh harmonic s] with t hgood
      obtain ⟨f, ⟨hf, hc⟩, _⟩ := hgood
      obtain ⟨p, hp, hu⟩ := existsUnique_distinguished_generation t f hf hc n
      symm
      rw [tsum_eq_single p.2]
      · simp only [ite_eq_left hp]
      · intro z hzp
        have hz : (t (List.ofFn z)).any Sum.isRight ≠ true := by
          intro hz
          exact hzp (congrArg Prod.snd (hu ((), z) hz))
        exact ite_eq_right hz
    _ = ∑' z : Fin n → ι, ∫⁻ t,
        (if (t (List.ofFn z)).any Sum.isRight = true then
          g (fun k p => (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) else 0)
        ∂treeKernel Q hh harmonic (some (Sum.inr s)) :=
      lintegral_tsum (fun z => (hG z).aemeasurable)
    _ = ∑' z : Fin n → ι, ∫⁻ t,
        addressWeight h n z (fun k p => t (List.ofFn p.2)) *
          g (fun k p => t (List.ofFn p.2)) ∂State.treeKernel Q (some s.1) := by
      apply tsum_congr
      intro z
      exact lintegral_treeKernel_fixedAddress Q hh harmonic s n z hg
    _ = _ := by
      have hprod (z : Fin n → ι) : Measurable (fun t : List ι → Option S =>
          addressWeight h n z (fun k p => t (List.ofFn p.2)) *
            g (fun k p => t (List.ofFn p.2))) :=
        ((measurable_addressWeight hh n z).comp ht).mul (hg.comp ht)
      rw [← lintegral_tsum (fun z => (hprod z).aemeasurable)]
      apply lintegral_congr
      intro t
      exact ENNReal.tsum_mul_right

/-- The joint finite-history law on a fixed terminal-spine event (Shi (4.12)). -/
theorem treeKernel_fixedAddress_measure {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) (z : Fin n → ι) :
    ((treeKernel Q hh harmonic (some (Sum.inr s))).restrict
      {t | (t (List.ofFn z)).any Sum.isRight = true}).map
      (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) =>
        (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) =
    ((State.treeKernel Q (some s.1)).map
      (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) => t (List.ofFn p.2))).withDensity
        (addressWeight h n z) := by
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  have he : Measurable (fun t : List ι → Option E =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) =>
        (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) := by
    have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
      measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
    fun_prop
  have ht : Measurable (fun t : List ι → Option S =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) := by fun_prop
  have htag : Measurable (fun o : Option E => o.any Sum.isRight) :=
    measurable_option_elim false (measurable_const.sumElim measurable_const)
  have hA : MeasurableSet {t : List ι → Option E |
      (t (List.ofFn z)).any Sum.isRight = true} :=
    (MeasurableSet.singleton true).preimage (htag.comp (measurable_pi_apply _))
  apply Measure.ext_of_lintegral
  intro g hg
  have hWg : Measurable (fun x : Π k : Iic n,
      (Unit × (Fin k.1 → ι)) → Option S => addressWeight h n z x * g x) :=
    (measurable_addressWeight hh n z).mul hg
  rw [lintegral_map hg he, ← lintegral_indicator hA,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_addressWeight hh n z) hg]
  simp only [Pi.mul_apply, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [lintegral_map hWg ht]
  exact lintegral_treeKernel_fixedAddress Q hh harmonic s n z hg

/-- The finite-generation tree density has expectation one (normalization in Shi Lemma 4.1). -/
theorem lintegral_totalWeight {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ) :
    (∫⁻ t, totalWeight h n (fun _k p => t (List.ofFn p.2))
      ∂State.treeKernel Q (some s.1)) = 1 := by
  let E := S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}
  have he : Measurable (fun t : List ι → Option E =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) =>
        (t (List.ofFn p.2)).map (Sum.elim id Subtype.val)) := by
    have hm : Measurable (fun o : Option E => o.map (Sum.elim id Subtype.val)) :=
      measurable_option_map (measurable_id.sumElim measurable_subtype_coe)
    fun_prop
  have ht : Measurable (fun t : List ι → Option S =>
      fun k : Iic n => fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) := by fun_prop
  rw [← lintegral_map (measurable_totalWeight hh n) ht]
  have hl := congrArg (fun μ => ∫⁻ _x, (1 : ℝ≥0∞) ∂μ)
    (treeKernel_finiteHistory Q hh harmonic s n)
  rw [lintegral_map measurable_const he,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_totalWeight hh n) measurable_const] at hl
  simpa only [Pi.mul_apply, mul_one, lintegral_const, measure_univ] using hl.symm

/-- Shi Theorem 4.3: finite-generation densities identify the complete untyped tree law.
This uses projective-limit uniqueness and does not assert a global density at infinity. -/
theorem eq_treeKernel_marginal_of_finiteHistory {S ι : Type*} [MeasurableSpace S]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (ν : Measure (List ι → Option S))
    [IsProbabilityMeasure ν]
    (hν : ∀ n, ν.map (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) => t (List.ofFn p.2)) =
      ((State.treeKernel Q (some s.1)).map
        (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) => t (List.ofFn p.2))).withDensity
          (totalWeight h n)) :
    ν = (treeKernel Q hh harmonic (some (Sum.inr s))).map
      (fun t u => (t u).map (Sum.elim id Subtype.val)) := by
  let ρ := (treeKernel Q hh harmonic (some (Sum.inr s))).map
    (fun t u => (t u).map (Sum.elim id Subtype.val))
  let G (t : List ι → Option S) (k : ℕ) (p : Unit × (Fin k → ι)) := t (List.ofFn p.2)
  have hG : Measurable G := by fun_prop
  have herase : Measurable (fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun u => (t u).map (Sum.elim id Subtype.val)) :=
    Step.map_measurable (measurable_id.sumElim measurable_subtype_coe)
  have hpref : ∀ n, (ν.map G).map (frestrictLe n) = (ρ.map G).map (frestrictLe n) := by
    intro n
    have ht : Measurable (fun t : List ι → Option S =>
        fun k : Iic n => fun p : Unit × (Fin k.1 → ι) => t (List.ofFn p.2)) := by fun_prop
    have hρ : ρ.map (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) =>
        t (List.ofFn p.2)) =
        ((State.treeKernel Q (some s.1)).map
          (fun t (k : Iic n) (p : Unit × (Fin k.1 → ι)) =>
            t (List.ofFn p.2))).withDensity (totalWeight h n) := by
      rw [Measure.map_map ht herase]
      exact treeKernel_finiteHistory Q hh harmonic s n
    exact (Measure.map_map (measurable_frestrictLe n) hG).trans
      ((hν n).trans (hρ.symm.trans (Measure.map_map (measurable_frestrictLe n) hG).symm))
  let family (I : Finset ℕ) := (ρ.map G).map I.restrict
  have hfam : IsProjectiveMeasureFamily
      (α := fun k : ℕ => (Unit × (Fin k → ι)) → Option S) family := by
    intro I J hJI
    have hI : Measurable (fun x : Π k : ℕ, (Unit × (Fin k → ι)) → Option S =>
        fun k : I => x k) := by fun_prop
    have hR : Measurable (fun x : Π k : I, (Unit × (Fin k.1 → ι)) → Option S =>
        fun k : J => x ⟨k.1, hJI k.2⟩) := by fun_prop
    exact (Measure.map_map hR hI (μ := ρ.map G)).symm
  have hνproj : IsProjectiveLimit
      (α := fun k : ℕ => (Unit × (Fin k → ι)) → Option S) (ν.map G) family :=
    (isProjectiveLimit_nat_iff
      (X := fun k => (Unit × (Fin k → ι)) → Option S) hfam _).mpr hpref
  have hpaths : ν.map G = ρ.map G := hνproj.unique (fun _ => rfl)
  let read (x : Π k : ℕ, (Unit × (Fin k → ι)) → Option S) (u : List ι) :=
    x u.length ((), u.get)
  have hread : Measurable read := by fun_prop
  have hback : read ∘ G = id := by
    funext t u
    exact congrArg t (List.ofFn_get u)
  have heq := congrArg (Measure.map read) hpaths
  rw [Measure.map_map hread hG, Measure.map_map hread hG, hback, Measure.map_id,
    Measure.map_id] at heq
  exact heq

end ProbabilityTheory.BranchingProcess.Spine

end
