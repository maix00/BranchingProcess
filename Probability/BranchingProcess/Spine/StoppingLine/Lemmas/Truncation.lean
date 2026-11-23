/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingProcess.Spine.StoppingLine.Mass
import Probability.BranchingProcess.Spine.Tree.Density.FiniteGeneration
import Probability.Process.Tree.Line.Optional
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Proof support for the frozen line-mass martingale

## Internal proof declarations

In `ProbabilityTheory.BranchingProcess.Spine.StoppingLine`:

* `measurable_line_test` observes the strict-ancestor non-entrance test at the
  current generation for a simple line.
* `lintegral_boundary_survival` proves, on every generation event `B`,
  `∫_B A_n + ∫_B U_(n+1) = ∫_B U_n`, with `A_n` the boundary mass and
  `U_n` the unexited mass. This is the one-step mass recursion.
* `measurable_generation_cut` checks measurability of the particular
  fixed-address density sums used in that recursion.
* `lintegral_generation_cut_le_one` bounds their expectations by
  `E[totalWeight h n] = 1`.

This assembles the generation-density proof of the mass recursion in
Biggins–Kyprianou, *Measure change in multitype branching* (2004), Lemma 14.3,
pp. 578–579, DOI 10.1239/aap/1086957585. Single-file tactical support is private.
-/

@[expose] section

namespace ProbabilityTheory.BranchingProcess.Spine.StoppingLine

open Classical MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris Finset
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

private lemma lintegral_generation_test
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ)
    (C : List ι → (List ι → Option S) → Prop)
    (hC : ∀ u, MeasurableSet[State.treeFiltration u.length] {t | C u t})
    {B : Set (List ι → Option S)} (hB : MeasurableSet[State.treeFiltration n] B) :
    (∫⁻ t in B, ∑' z : Fin n → ι,
      if C (List.ofFn z) t then addressWeight h n z (State.treeHistory n t) else 0
      ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t, ∑' z : Fin n → ι, if (t (List.ofFn z)).any Sum.isRight = true then
      (if C (List.ofFn z) (fun v => (t v).map (Sum.elim id Subtype.val)) ∧
        (fun v => (t v).map (Sum.elim id Subtype.val)) ∈ B then 1 else 0) else 0
      ∂treeKernel Q hh harmonic (some (Sum.inr s)) := by
  have hm (z : Fin n → ι) : Measurable[State.treeFiltration n]
      (fun t : List ι → Option S => if C (List.ofFn z) t ∧ t ∈ B then (1 : ℝ≥0∞) else 0) :=
    by
      have hc : MeasurableSet[State.treeFiltration n] {t | C (List.ofFn z) t} := by
        have hc := hC (List.ofFn z)
        rw [List.length_ofFn] at hc
        exact hc
      exact measurable_const.ite (hc.inter hB) measurable_const
  choose g hg hge using fun z => (hm z).exists_eq_measurable_comp
  have hi := lintegral_generationPayoff_eq Q hh harmonic s n g hg
  have hgread (z : Fin n → ι) (t : List ι → Option S) :
      g z (State.treeHistory n t) = if C (List.ofFn z) t ∧ t ∈ B then 1 else 0 :=
    (congrFun (hge z) t).symm
  have hleft : (∫⁻ t in B, ∑' z : Fin n → ι,
      if C (List.ofFn z) t then addressWeight h n z (State.treeHistory n t) else 0
        ∂State.treeKernel Q (some s.1)) =
      ∫⁻ t, ∑' z : Fin n → ι,
        addressWeight h n z (State.treeHistory n t) * g z (State.treeHistory n t)
          ∂State.treeKernel Q (some s.1) := by
    rw [← lintegral_indicator ((State.treeFiltration.le n) _ hB)]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ B
    · simp only [Set.indicator_of_mem ht]
      apply tsum_congr
      intro z
      rw [hgread]
      by_cases hc : C (List.ofFn z) t <;> simp [hc, ht]
    · simp only [Set.indicator_of_notMem ht]
      simp only [hgread, ht, and_false, ite_false, mul_zero, tsum_zero]
  refine hleft.trans (hi.trans ?_)
  apply lintegral_congr
  intro t
  apply tsum_congr
  intro z
  change (if (t (List.ofFn z)).any Sum.isRight = true then
    g z (State.treeHistory n (fun v => (t v).map (Sum.elim id Subtype.val))) else 0) = _
  rw [hgread]

omit [MeasurableSpace S] [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] in
private lemma tagged_generation_sum {h : S → ℝ≥0∞}
    (t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
    (f : ℕ → ι) (hf : IsRay (distinguishedNodes t) f)
    (hc : distinguishedNodes t = Set.range (lineagePrefix f))
    (n : ℕ) (g : List ι → ℝ≥0∞) :
    (∑' z : Fin n → ι, if (t (List.ofFn z)).any Sum.isRight = true then
      g (List.ofFn z) else 0) = g (lineagePrefix f n) := by
  obtain ⟨p, hp, hu⟩ := existsUnique_distinguished_generation t f hf hc n
  have hEq : List.ofFn p.2 = lineagePrefix f n := by
    have hmem : List.ofFn p.2 ∈ distinguishedNodes t := hp
    rw [hc] at hmem
    obtain ⟨m, hm⟩ := hmem
    have hmn : m = n := by
      simpa only [length_lineagePrefix, List.length_ofFn] using congrArg List.length hm
    exact hm.symm.trans (congrArg (lineagePrefix f) hmn)
  rw [tsum_eq_single p.2, ite_eq_left hp, hEq]
  intro z hzp
  apply ite_eq_right
  intro hz
  exact hzp (congrArg Prod.snd (hu ((), z) hz))

omit [MeasurableSpace S] [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] in
private lemma ray_take (f : ℕ → ι) {n k : ℕ} (hk : k ≤ n) :
    (lineagePrefix f n).take k = lineagePrefix f k := by
  have hp := List.prefix_iff_eq_take.mp (lineagePrefix_prefix f hk)
  simpa only [length_lineagePrefix] using hp.symm

omit [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] in
lemma measurable_line_test
    {past : Set (Unit × List ι) → MeasurableSpace (List ι → Option S)}
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsOptionalLine past L) (hs : hL.IsSimple State.treeFiltration)
    (u : List ι) :
    MeasurableSet[State.treeFiltration u.length] {t | ∀ k < u.length, ((), u.take k) ∉ L t} := by
  have heq : {t : List ι → Option S | ∀ k < u.length, ((), u.take k) ∉ L t} =
      ⋂ k : ℕ, {t | k < u.length → ((), u.take k) ∉ L t} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : k < u.length
  · have hlen : (u.take k).length ≤ u.length := by
      simp only [List.length_take]
      omega
    have hm : MeasurableSet[State.treeFiltration u.length] {t | ((), u.take k) ∈ L t} :=
      (State.treeFiltration.mono hlen) _ (hs ((), u.take k))
    simpa only [hk, true_implies, Set.compl_ofPred] using hm.compl
  · simp only [hk, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

lemma lintegral_boundary_survival
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞})
    {past : Set (Unit × List ι) → MeasurableSpace (List ι → Option S)}
    {L : (List ι → Option S) → Set (Unit × List ι)}
    (hL : Tree.IsOptionalLine past L) (hs : hL.IsSimple State.treeFiltration)
    (n : ℕ) {B : Set (List ι → Option S)} (hB : MeasurableSet[State.treeFiltration n] B) :
    (∫⁻ t in B, generationMass h L n t ∂State.treeKernel Q (some s.1)) +
      (∫⁻ t in B, unexitedMass h L (n + 1) t ∂State.treeKernel Q (some s.1)) =
    ∫⁻ t in B, unexitedMass h L n t ∂State.treeKernel Q (some s.1) := by
  let C (u : List ι) (t : List ι → Option S) := ∀ k < u.length, ((), u.take k) ∉ L t
  have hC := measurable_line_test hL hs
  have hbn := lintegral_generation_test Q hh harmonic s n C hC hB
  have hbn1 := lintegral_generation_test Q hh harmonic s (n + 1) C hC
    ((State.treeFiltration.mono n.le_succ) _ hB)
  have han := lintegral_generation_test Q hh harmonic s n
    (fun u t => ((), u) ∈ L t) (fun u => hs ((), u)) hB
  simp only [C, List.length_ofFn] at hbn hbn1
  change (∫⁻ t in B, generationMass h L n t ∂State.treeKernel Q (some s.1)) = _ at han
  have hun (m : ℕ) : unexitedMass h L m =
      (fun t => ∑' z : Fin m → ι,
        if ∀ k < m, ((), (List.ofFn z).take k) ∉ L t then
          addressWeight h m z (State.treeHistory m t) else 0) := by
    funext t
    unfold unexitedMass
    apply tsum_congr
    intro z
    by_cases hc : ∀ k < m, ((), (List.ofFn z).take k) ∉ L t <;> simp [hc]
  rw [hun n, hun (n + 1), han, hbn1, hbn]
  have he : Measurable (fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun v => (t v).map (Sum.elim id Subtype.val)) := by
    have hm := measurable_option_map (measurable_id.sumElim
      (measurable_subtype_coe : Measurable (Subtype.val : {s // h s ≠ 0 ∧ h s ≠ ∞} → S)))
    fun_prop
  have ht : Measurable (fun o : Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      o.any Sum.isRight) := measurable_option_elim false (measurable_const.sumElim measurable_const)
  have hm : Measurable (fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      ∑' z : Fin n → ι, if (t (List.ofFn z)).any Sum.isRight = true then
        (if ((), List.ofFn z) ∈ L (fun v => (t v).map (Sum.elim id Subtype.val)) ∧
          (fun v => (t v).map (Sum.elim id Subtype.val)) ∈ B then (1 : ℝ≥0∞) else 0) else 0) := by
    apply Measurable.tsum
    intro z
    refine Measurable.ite ((measurableSet_singleton true).preimage
      (ht.comp (measurable_pi_apply _))) ?_ measurable_const
    exact measurable_const.ite
      (((hL.toIsRandomLine.measurableSet_mem _).preimage he).inter
        (((State.treeFiltration.le n) _ hB).preimage he)) measurable_const
  rw [← lintegral_add_left hm]
  apply lintegral_congr_ae
  filter_upwards [ae_treeKernel_unique_spine Q hh harmonic s] with t ht
  obtain ⟨f, ⟨hf, hc⟩, _⟩ := ht
  have ha := tagged_generation_sum t f hf hc n (fun u =>
    if ((), u) ∈ L (fun v => (t v).map (Sum.elim id Subtype.val)) ∧
      (fun v => (t v).map (Sum.elim id Subtype.val)) ∈ B then 1 else 0)
  have hb := tagged_generation_sum t f hf hc (n + 1) (fun u =>
    if (∀ k < n + 1, ((), u.take k) ∉ L (fun v => (t v).map (Sum.elim id Subtype.val))) ∧
      (fun v => (t v).map (Sum.elim id Subtype.val)) ∈ B then 1 else 0)
  have hd := tagged_generation_sum t f hf hc n (fun u =>
    if (∀ k < n, ((), u.take k) ∉ L (fun v => (t v).map (Sum.elim id Subtype.val))) ∧
      (fun v => (t v).map (Sum.elim id Subtype.val)) ∈ B then 1 else 0)
  rw [ha, hb, hd]
  have hbefore (m : ℕ) :
      (∀ k < m, ((), (lineagePrefix f m).take k) ∉ L
        (fun v => (t v).map (Sum.elim id Subtype.val))) ↔
      ∀ k < m, ((), lineagePrefix f k) ∉ L
        (fun v => (t v).map (Sum.elim id Subtype.val)) := by
    constructor <;> intro hb k hk
    · simpa only [ray_take f (Nat.le_of_lt hk)] using hb k hk
    · simpa only [ray_take f (Nat.le_of_lt hk)] using hb k hk
  simp only [hbefore]
  have ha : ((), lineagePrefix f n) ∈ L
      (fun v => (t v).map (Sum.elim id Subtype.val)) →
      ∀ k < n, ((), lineagePrefix f k) ∉ L
        (fun v => (t v).map (Sum.elim id Subtype.val)) := by
    intro hn k hk hkmem
    have heq := (hL.isLine _).eq hkmem hn ⟨rfl, lineagePrefix_prefix f (Nat.le_of_lt hk)⟩
    have hkn : k = n := by
      simpa only [length_lineagePrefix] using
        congrArg (fun p : Unit × List ι => p.2.length) heq
    omega
  have hb : (∀ k < n + 1, ((), lineagePrefix f k) ∉ L
      (fun v => (t v).map (Sum.elim id Subtype.val))) ↔
      (∀ k < n, ((), lineagePrefix f k) ∉ L
        (fun v => (t v).map (Sum.elim id Subtype.val))) ∧
      ((), lineagePrefix f n) ∉ L (fun v => (t v).map (Sum.elim id Subtype.val)) := by
    constructor
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩
    · rintro ⟨h, hn⟩ k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · exact h k hk
      · exact hn
  simp only [hb]
  by_cases htB : (fun v => (t v).map (Sum.elim id Subtype.val)) ∈ B
  · simp only [htB, and_true]
    by_cases hn : ((), lineagePrefix f n) ∈ L
        (fun v => (t v).map (Sum.elim id Subtype.val))
    · simp [hn]
      exact ha hn
    · by_cases hprev : ∀ k < n, ((), lineagePrefix f k) ∉ L
          (fun v => (t v).map (Sum.elim id Subtype.val)) <;> simp [hn, hprev]
  · simp only [htB, and_false, ite_false, zero_add]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma measurable_generation_cut {h : S → ℝ≥0∞} (hh : Measurable h) (n : ℕ)
    (C : (Fin n → ι) → (List ι → Option S) → Prop)
    (hC : ∀ z, MeasurableSet[State.treeFiltration n] {t | C z t}) :
    Measurable[State.treeFiltration n] (fun t : List ι → Option S =>
      ∑' z : Fin n → ι, if C z t then addressWeight h n z (State.treeHistory n t) else 0) := by
  let : MeasurableSpace (List ι → Option S) := State.treeFiltration n
  apply Measurable.tsum
  intro z
  exact ((measurable_addressWeight hh n z).comp
    (Measurable.of_comap_le le_rfl)).ite (hC z) measurable_const

lemma lintegral_generation_cut_le_one
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ → (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (s : {s // h s ≠ 0 ∧ h s ≠ ∞}) (n : ℕ)
    (C : (Fin n → ι) → (List ι → Option S) → Prop) :
    (∫⁻ t, ∑' z : Fin n → ι,
      if C z t then addressWeight h n z (State.treeHistory n t) else 0
        ∂State.treeKernel Q (some s.1)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ t, totalWeight h n (State.treeHistory n t) ∂State.treeKernel Q (some s.1) := by
      apply lintegral_mono
      intro t
      apply tsum_le_tsum
      intro z
      dsimp only
      split_ifs <;> simp
    _ = 1 := lintegral_totalWeight Q hh harmonic s n

end ProbabilityTheory.BranchingProcess.Spine.StoppingLine
