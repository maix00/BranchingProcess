/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.BoundedOffspring
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtreeVector
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
import Probability.Independence.ConditionalIntegral

/-!
# Internal finite-slot address coding

This module contains the address, encode/decode, and level-root facts used to
construct the finite-slot population process in the parent `Coupling` module.
The coding is specific to that construction and is kept in the parent's
`Lemmas/` layer as non-reusable proof support.

## Public declarations

None. The address maps and ordinary lemmas below only support the construction
and proof of the finite-slot coupling; they do not form a standalone API.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris

/-- A successor slot used to fill an inactive binary branch. -/
noncomputable def finiteSlotSuccessor
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] (x : α) : α := by
  letI : SuccOrder α := LinearLocallyFiniteOrder.succOrder α
  exact Order.succ x

lemma finiteSlotSuccessor_gt
    {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] (x : α) :
    x < finiteSlotSuccessor x := by
  letI : SuccOrder α := LinearLocallyFiniteOrder.succOrder α
  change x < Order.succ x
  apply Order.lt_succ_of_not_isMax
  obtain ⟨y, hxy⟩ := NoMaxOrder.exists_gt x
  exact not_isMax_of_lt hxy

/-- The source slot assigned to one of the two finite offspring labels.
Selected children occupy the first positions in slot order. Missing positions
are sent to successors of the first selected slot, which provides distinct
addresses for inactive binary branches. -/
noncomputable def finiteSlotAddress
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) (i : Fin 2) : α := by
  exact if i.val = 0 then firstSelectedSlot S ξ else
    if 2 ≤ (S ξ).card then secondSelectedSlot S ξ else
      finiteSlotSuccessor (firstSelectedSlot S ξ)

@[simp] lemma finiteSlotAddress_zero
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) :
    finiteSlotAddress S ξ 0 = firstSelectedSlot S ξ := by
  simp [finiteSlotAddress]

@[simp] lemma finiteSlotAddress_one
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) :
    finiteSlotAddress S ξ 1 =
      if 2 ≤ (S ξ).card then secondSelectedSlot S ξ else
        finiteSlotSuccessor (firstSelectedSlot S ξ) := by
  rfl

/-- Under the capacity-two bound, the two finite labels have distinct source
slots, including when the selected family is empty or a singleton. -/
lemma finiteSlotAddress_injective
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) :
    Function.Injective (finiteSlotAddress S ξ) := by
  classical
  have h01 : finiteSlotAddress S ξ 0 ≠ finiteSlotAddress S ξ 1 := by
    rw [finiteSlotAddress_zero, finiteSlotAddress_one]
    by_cases htwo : 2 ≤ (S ξ).card
    · rw [ite_eq_left htwo]
      exact (secondSelectedSlot_mem_of_card S ξ htwo).2
    · rw [ite_eq_right htwo]
      exact ne_of_lt (finiteSlotSuccessor_gt _)
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (h01 hij)
  · exact False.elim (h01 hij.symm)
  · rfl

/-- Every selected source slot is represented by an active binary label when
the selector keeps at most two children. -/
lemma finiteSlotAddress_exists_of_mem
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X)
    (hcapacity : (S ξ).card ≤ 2) {i : α} (hi : i ∈ S ξ) :
    ∃ j : Fin 2, j.val < (S ξ).card ∧ finiteSlotAddress S ξ j = i := by
  classical
  let f := firstSelectedSlot S ξ
  have hfirst : f ∈ S ξ := firstSelectedSlot_mem S ξ ⟨i, hi⟩
  by_cases hfi : i = f
  · refine ⟨0, ?_, ?_⟩
    · have hpos : 0 < (S ξ).card := Finset.card_pos.mpr ⟨i, hi⟩
      simp [hpos]
    · simpa [finiteSlotAddress_zero, f, hfi]
  · have htwo : 2 ≤ (S ξ).card := by
      by_contra h
      have hle : (S ξ).card ≤ 1 := by omega
      have heq := (Finset.card_le_one_iff).mp hle hi hfirst
      exact hfi heq
    have hif : f ≠ i := Ne.symm hfi
    have hcard : (S ξ).card = 2 := by omega
    have hpairSub : ({f, i} : Finset α) ⊆ S ξ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hfirst
      · exact hi
    have hpairCard : ({f, i} : Finset α).card = 2 := by
      simp [hif]
    have hpair : ({f, i} : Finset α) = S ξ :=
      Finset.eq_of_subset_of_card_le hpairSub (by rw [hpairCard, hcard])
    have herase : (S ξ).erase f = {i} := by
      rw [← hpair]
      simp [hif]
    have hsecond : secondSelectedSlot S ξ = i := by
      simp [secondSelectedSlot, herase, f]
    refine ⟨1, ?_, ?_⟩
    · simp [hcard]
    · rw [finiteSlotAddress_one, ite_eq_left htwo, hsecond]

/-- A path belongs to the selected population exactly when each of its
successive slots is retained by the selector at its parent. -/
def selectedAlong {α X : Type*}
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    TreeNode α → TreeNode α → Prop
  | _, [] => True
  | v, i :: p => i ∈ S (ω v) ∧ selectedAlong S ω (v ++ [i]) p

lemma selectedAlong_append_singleton
    {α X : Type*} (S : Step.FiniteSelection α X)
    (ω : Mark α (Step α X)) :
    ∀ (v p : TreeNode α) (i : α),
      selectedAlong S ω v (p ++ [i]) ↔
        selectedAlong S ω v p ∧ i ∈ S (ω (v ++ p)) := by
  intro v p
  induction p generalizing v with
  | nil => intro i; simp [selectedAlong]
  | cons j p ih =>
      intro i
      have hpath : v ++ (j :: p) = (v ++ [j]) ++ p := by simp
      simp only [List.cons_append, selectedAlong]
      rw [ih]
      simp only [hpath, and_assoc]

/-- The recursive selected population is precisely the finite set of
same-generation paths retained edge by edge. -/
lemma mem_population_iff_length_selectedAlong
    {α X : Type*} (S : Step.FiniteSelection α X)
    (ω : Mark α (Step α X)) :
    ∀ n u, u ∈ StepSelection.population S n ω ↔
      u.length = n ∧ selectedAlong S ω [] u := by
  intro n
  induction n with
  | zero =>
      intro u
      rw [StepSelection.population_zero]
      simp only [Finset.mem_singleton]
      constructor
      · intro hu
        subst u
        simp [selectedAlong]
      · rintro ⟨hu, _⟩
        exact List.length_eq_zero_iff.mp hu
  | succ n ih =>
      intro q
      rw [StepSelection.population_succ, StepSelection.mem_grow_iff]
      constructor
      · rintro ⟨u, hu, i, hi, rfl⟩
        have hu' := (ih u).mp hu
        have hfrontier : frontierMarks n ω u = ω u := by
          simp [frontierMarks, hu'.1]
        refine ⟨by simp [hu'.1], ?_⟩
        rw [selectedAlong_append_singleton]
        exact ⟨hu'.2, hfrontier ▸ hi⟩
      · rintro ⟨hqLength, hqSelected⟩
        have hqne : q ≠ [] := by
          intro h
          simp [h] at hqLength
        let i := q.getLast hqne
        have hsplit : q.dropLast ++ [i] = q := by
          simpa [i] using List.dropLast_append_getLast hqne
        have hselected : selectedAlong S ω [] (q.dropLast ++ [i]) := by
          simpa [hsplit] using hqSelected
        have hparts := (selectedAlong_append_singleton S ω [] q.dropLast i).mp
          hselected
        have hparentLength : q.dropLast.length = n := by
          rw [List.length_dropLast]
          omega
        have hparent : q.dropLast ∈ StepSelection.population S n ω :=
          (ih q.dropLast).mpr ⟨hparentLength, hparts.1⟩
        have hfrontier :
            frontierMarks n ω q.dropLast = ω q.dropLast := by
          simp [frontierMarks, hparentLength]
        exact ⟨q.dropLast, hparent, i, hfrontier ▸ hparts.2, hsplit.symm⟩

/-- The finite label survives in the coded offspring step exactly when its
source address is selected. -/
lemma finiteSlotAddress_mem_iff
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X)
    (hcapacity : (S ξ).card ≤ 2) (i : Fin 2) :
    finiteSlotAddress S ξ i ∈ S ξ ↔ i.val < (S ξ).card := by
  classical
  letI : SuccOrder α := LinearLocallyFiniteOrder.succOrder α
  fin_cases i
  · simp only [finiteSlotAddress_zero]
    by_cases hnonempty : (S ξ).Nonempty
    · have hfirst := firstSelectedSlot_mem S ξ hnonempty
      have hpos : 0 < (S ξ).card := Finset.card_pos.mpr hnonempty
      simp [hfirst, hpos]
    · have hcard : (S ξ).card = 0 := by
        simpa [Finset.card_pos] using hnonempty
      have hS : S ξ = ∅ := Finset.card_eq_zero.mp hcard
      simp [firstSelectedSlot, hS]
  · simp only [finiteSlotAddress_one]
    by_cases htwo : 2 ≤ (S ξ).card
    · have hsecond := secondSelectedSlot_mem_of_card S ξ htwo
      have hlt : 1 < (S ξ).card := by omega
      simp [htwo, hsecond.1, hlt]
    · have hcard : (S ξ).card ≤ 1 := by omega
      by_cases hnonempty : (S ξ).Nonempty
      · have hfirst := firstSelectedSlot_mem S ξ hnonempty
        have hcard1 : (S ξ).card = 1 := by
          have hpos := Finset.card_pos.mpr hnonempty
          omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
        have hfirstx : firstSelectedSlot S ξ = x := by
          simp [firstSelectedSlot, hx]
        have hnotmem : finiteSlotSuccessor (firstSelectedSlot S ξ) ∉ S ξ := by
          rw [hx]
          simp only [Finset.mem_singleton]
          intro heq
          exact (ne_of_lt (finiteSlotSuccessor_gt (firstSelectedSlot S ξ)))
            (hfirstx.trans heq.symm)
        simp [htwo, hcard1, hnotmem]
      · have hcard0 : (S ξ).card = 0 := by
          simpa [Finset.card_pos] using hnonempty
        have hfirst : firstSelectedSlot S ξ = ⊥ := by
          simp [firstSelectedSlot, hnonempty]
        simp [htwo, hcard0, hfirst, Finset.card_eq_zero.mp hcard0]

/-- A fixed binary label's source slot is a measurable function of the
offspring mark. -/
lemma finiteSlotAddress_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (i : Fin 2) : Measurable (finiteSlotAddress S · i) := by
  classical
  have hfirst : Measurable (firstSelectedSlot S) :=
    firstSelectedSlot_measurable S hS
  have hsecond : Measurable (secondSelectedSlot S) :=
    secondSelectedSlot_measurable S hS
  have hcard : Measurable (fun ξ : Step α X => (S ξ).card) :=
    (measurable_of_countable fun t : Finset α => t.card).comp hS
  have hsplit : MeasurableSet {ξ : Step α X | 2 ≤ (S ξ).card} := by
    change MeasurableSet
      ((fun ξ : Step α X => (S ξ).card) ⁻¹' Set.Ici 2)
    exact hcard measurableSet_Ici
  by_cases hi : i.val = 0
  · simpa [finiteSlotAddress, hi] using hfirst
  · have hsucc : Measurable
        (fun ξ : Step α X => finiteSlotSuccessor (firstSelectedSlot S ξ)) :=
      (measurable_of_countable fun a : α => finiteSlotSuccessor a).comp hfirst
    have htail : Measurable
        (fun ξ : Step α X =>
          if 2 ≤ (S ξ).card then secondSelectedSlot S ξ else
            finiteSlotSuccessor (firstSelectedSlot S ξ)) :=
      Measurable.ite hsplit hsecond hsucc
    simpa [finiteSlotAddress, hi] using htail

/-- Decode a finite-slot address by following, at each prefix, the source
slot assigned to the next binary label. The decoder is defined on inactive
labels too, which keeps the map injective on every level. -/
noncomputable def finiteSlotDecode
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (u : List (Fin 2)) : TreeNode α :=
  u.foldl (fun p i => p ++ [finiteSlotAddress S (ω p) i]) []

/-- Appending one binary label appends its selected source slot to the
previously decoded prefix. -/
@[simp] lemma finiteSlotDecode_append_singleton
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (u : List (Fin 2)) (i : Fin 2) :
    finiteSlotDecode S ω (u ++ [i]) =
      finiteSlotDecode S ω u ++
        [finiteSlotAddress S (ω (finiteSlotDecode S ω u)) i] := by
  simp [finiteSlotDecode, List.foldl_append]

/-- The finite-slot offspring field read along the decoded source addresses. -/
noncomputable def finiteSlotCodedStepField
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    StepField (Fin 2) PUnit.{1} :=
  fun u => finiteOffspringStep S (ω (finiteSlotDecode S ω u))

/-- A binary path survives in the coded finite-slot field exactly when its
decoded source path uses selected children at every step. -/
lemma finiteSlotDecode_surviveAlong_iff_selectedAlong
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) :
    ∀ u : TreeNode (Fin 2),
      Combinatorics.Branching.surviveAlong
        (finiteSlotCodedStepField S ω) [] u ↔
      selectedAlong S ω [] (finiteSlotDecode S ω u) := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
      simp [Combinatorics.Branching.surviveAlong, finiteSlotCodedStepField,
        selectedAlong, finiteSlotDecode]
  | append_singleton u i ih =>
      rw [Combinatorics.Branching.surviveAlong_append_singleton,
        finiteSlotDecode_append_singleton,
        selectedAlong_append_singleton, ih]
      simp only [List.nil_append]
      have hslot := finiteSlotAddress_mem_iff S
        (ω (finiteSlotDecode S ω u)) (hcapacity _) i
      have hchild :
          survive (finiteSlotCodedStepField S ω u) i ↔
            finiteSlotAddress S (ω (finiteSlotDecode S ω u)) i ∈
              S (ω (finiteSlotDecode S ω u)) := by
        change survive (finiteOffspringStep S
          (ω (finiteSlotDecode S ω u))) i ↔ _
        calc
          survive (finiteOffspringStep S
              (ω (finiteSlotDecode S ω u))) i ↔
              i.val < (S (ω (finiteSlotDecode S ω u))).card := by
                rw [Combinatorics.Branching.survive_iff_ne_none]
                simp [finiteOffspringStep]
          _ ↔ finiteSlotAddress S (ω (finiteSlotDecode S ω u)) i ∈
              S (ω (finiteSlotDecode S ω u)) := hslot.symm
      rw [hchild]

/-- Select the binary label assigned to a selected source slot. -/
noncomputable def finiteSlotRank
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) (i : α) : Fin 2 :=
  if finiteSlotAddress S ξ 0 = i then 0 else 1

lemma finiteSlotRank_address
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X)
    (hcapacity : (S ξ).card ≤ 2) {i : α} (hi : i ∈ S ξ) :
    finiteSlotAddress S ξ (finiteSlotRank S ξ i) = i ∧
      (finiteSlotRank S ξ i).val < (S ξ).card := by
  classical
  obtain ⟨j, hj, hji⟩ := finiteSlotAddress_exists_of_mem S ξ hcapacity hi
  by_cases hfirst : finiteSlotAddress S ξ 0 = i
  · have hj0 : j = 0 := by
      by_contra hj0
      have hj1 : j = 1 := by
        fin_cases j <;> simp_all
      have hji0 := finiteSlotAddress_injective S ξ
        (hji.trans hfirst.symm)
      have hbad : (1 : Fin 2) = 0 := hj1.symm.trans hji0
      exact (by decide : (1 : Fin 2) ≠ 0) hbad
    subst j
    have hrank : finiteSlotRank S ξ i = 0 := by
      simp [finiteSlotRank, hfirst]
    rw [hrank]
    exact ⟨hji, hj⟩
  · have hj1 : j = 1 := by
      fin_cases j
      · exact False.elim (hfirst hji)
      · rfl
    subst j
    have hfirst' : firstSelectedSlot S ξ ≠ i := by
      simpa only [finiteSlotAddress_zero] using hfirst
    have hrank : finiteSlotRank S ξ i = 1 := by
      simp [finiteSlotRank, hfirst']
    rw [hrank]
    exact ⟨hji, hj⟩

/-- Extend a source prefix by the finite label assigned to each selected
source child. -/
noncomputable def finiteSlotEncodeFrom
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (v : TreeNode α) : TreeNode α → TreeNode (Fin 2)
  | [] => []
  | i :: p => finiteSlotRank S (ω v) i ::
      finiteSlotEncodeFrom S ω (v ++ [i]) p

/-- Encode a selected source path from the root by its binary slot labels. -/
noncomputable def finiteSlotEncode
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (p : TreeNode α) : TreeNode (Fin 2) :=
  finiteSlotEncodeFrom S ω [] p

/-- Decoding can start at an already decoded source prefix. -/
noncomputable def finiteSlotDecodeFrom
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (v : TreeNode α) (u : TreeNode (Fin 2)) : TreeNode α :=
  u.foldl (fun p i => p ++ [finiteSlotAddress S (ω p) i]) v

lemma finiteSlotDecode_eq_decodeFrom
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (u : TreeNode (Fin 2)) :
    finiteSlotDecode S ω u = finiteSlotDecodeFrom S ω [] u := rfl

@[simp] lemma finiteSlotDecodeFrom_append_singleton
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (v : TreeNode α) (u : TreeNode (Fin 2)) (i : Fin 2) :
    finiteSlotDecodeFrom S ω v (u ++ [i]) =
      finiteSlotDecodeFrom S ω v u ++
        [finiteSlotAddress S (ω (finiteSlotDecodeFrom S ω v u)) i] := by
  simp [finiteSlotDecodeFrom, List.foldl_append]

lemma finiteSlotEncodeFrom_length
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    ∀ (v p : TreeNode α),
      (finiteSlotEncodeFrom S ω v p).length = p.length := by
  intro v p
  induction p generalizing v with
  | nil => rfl
  | cons i p ih => simp [finiteSlotEncodeFrom, ih]

lemma finiteSlotDecodeFrom_encodeFrom
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) :
    ∀ (v p : TreeNode α),
      selectedAlong S ω v p →
        finiteSlotDecodeFrom S ω v (finiteSlotEncodeFrom S ω v p) = v ++ p := by
  intro v p
  induction p generalizing v with
  | nil => intro hp; simp [finiteSlotEncodeFrom, finiteSlotDecodeFrom]
  | cons i p ih =>
      intro hp
      rcases hp with ⟨hi, htail⟩
      have hrank := finiteSlotRank_address S (ω v) (hcapacity (ω v)) hi
      have hrest := ih (v := v ++ [i]) htail
      simp only [finiteSlotEncodeFrom, finiteSlotDecodeFrom, List.foldl_cons]
      rw [hrank.1]
      change finiteSlotDecodeFrom S ω (v ++ [i])
        (finiteSlotEncodeFrom S ω (v ++ [i]) p) = v ++ i :: p
      rw [hrest]
      simp

/-- The decoder preserves generation. -/
lemma finiteSlotDecode_length
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (u : List (Fin 2)) :
    (finiteSlotDecode S ω u).length = u.length := by
  unfold finiteSlotDecode
  have hfold : ∀ (v : List (Fin 2)) (p : TreeNode α),
      (v.foldl (fun q i => q ++ [finiteSlotAddress S (ω q) i]) p).length =
        p.length + v.length := by
    intro v
    induction v with
    | nil => intro p; simp
    | cons i v ih =>
        intro p
        simp only [List.foldl_cons]
        rw [ih]
        simp [List.length_append]
        omega
  simpa using hfold u []

/-- Every active coded address of length `n` decodes to the actual
N-selected population at generation `n`. -/
lemma finiteSlotDecode_mem_population_of_surviveAlong
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ)
    {u : TreeNode (Fin 2)} (hlen : u.length = n)
    (hactive : Combinatorics.Branching.surviveAlong
      (finiteSlotCodedStepField S ω) [] u) :
    finiteSlotDecode S ω u ∈ StepSelection.population S n ω := by
  apply (mem_population_iff_length_selectedAlong S ω n _).2
  refine ⟨?_, (finiteSlotDecode_surviveAlong_iff_selectedAlong
    S ω hcapacity u).mp hactive⟩
  rw [finiteSlotDecode_length, hlen]

/-- Every source path in the N-selected population has an active binary
address in the coded finite-slot tree. -/
lemma finiteSlotDecode_exists_of_mem_population
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ)
    {p : TreeNode α} (hp : p ∈ StepSelection.population S n ω) :
    ∃ u : TreeNode (Fin 2), u.length = n ∧
      Combinatorics.Branching.surviveAlong
        (finiteSlotCodedStepField S ω) [] u ∧
      finiteSlotDecode S ω u = p := by
  have hp' := (mem_population_iff_length_selectedAlong S ω n p).mp hp
  let u := finiteSlotEncode S ω p
  have huLength : u.length = n := by
    simp [u, finiteSlotEncode, finiteSlotEncodeFrom_length, hp'.1]
  have huDecode : finiteSlotDecode S ω u = p := by
    have h := finiteSlotDecodeFrom_encodeFrom S ω hcapacity [] p hp'.2
    rw [finiteSlotDecode_eq_decodeFrom]
    simpa [u, finiteSlotEncode] using h
  have huActive : Combinatorics.Branching.surviveAlong
      (finiteSlotCodedStepField S ω) [] u := by
    apply (finiteSlotDecode_surviveAlong_iff_selectedAlong
      S ω hcapacity u).2
    simpa [huDecode] using hp'.2
  exact ⟨u, huLength, huActive, huDecode⟩

/-- Decoding a binary address of length `n` only reads marks at depths below
`n`, so the resulting source address is observable at generation `n`. -/
lemma finiteSlotDecode_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) :
    ∀ u : List (Fin 2),
      Measurable[generationFiltration (M := Step α X) u.length]
        (fun ω : Mark α (Step α X) => finiteSlotDecode S ω u) := by
  intro u
  induction u using List.reverseRecOn with
  | nil => exact measurable_const
  | append_singleton u i ih =>
      have hprefix := ih.mono
        (generationFiltration (M := Step α X) |>.mono
          (Nat.le_succ u.length)) le_rfl
      have hmark : Measurable[
          generationFiltration (M := Step α X) (u.length + 1)]
          (fun ω : Mark α (Step α X) => ω (finiteSlotDecode S ω u)) :=
        selected_mark_measurable (M := Step α X) (u.length + 1)
          (fun ω => finiteSlotDecode S ω u) hprefix
          (fun ω => by rw [finiteSlotDecode_length]; exact Nat.lt_succ_self _)
      have hslot : Measurable[
          generationFiltration (M := Step α X) (u.length + 1)]
          (fun ω => finiteSlotAddress S (ω (finiteSlotDecode S ω u)) i) :=
        (finiteSlotAddress_measurable S hS i).comp hmark
      have happend : Measurable (fun p : TreeNode α × α => p.1 ++ [p.2]) :=
        measurable_of_countable _
      have hpair := hprefix.prodMk hslot
      have hresult : Measurable[
          generationFiltration (M := Step α X) (u.length + 1)]
          (fun ω : Mark α (Step α X) =>
            finiteSlotDecode S ω (u ++ [i])) := by
        convert happend.comp hpair using 1
        funext ω
        simp [Function.comp_def, finiteSlotDecode_append_singleton]
      change Measurable[
        generationFiltration (M := Step α X) ((u ++ [i]).length)]
        (fun ω : Mark α (Step α X) =>
          finiteSlotDecode S ω (u ++ [i]))
      rw [List.length_append, List.length_singleton]
      exact hresult

/-- At each fixed generation, distinct binary addresses decode to distinct
source addresses. -/
lemma finiteSlotDecode_injective_level
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    {u v : List (Fin 2)} (hlen : u.length = v.length)
    (hdecode : finiteSlotDecode S ω u = finiteSlotDecode S ω v) :
    u = v := by
  classical
  induction u using List.reverseRecOn generalizing v with
  | nil =>
      have hv : v = [] := by
        cases v with
        | nil => rfl
        | cons i v => simp at hlen
      simpa [hv]
  | append_singleton u i ih =>
      have hvne : v ≠ [] := by
        intro hv
        simp [hv] at hlen
      let j := v.getLast hvne
      have hsplit : v.dropLast ++ [j] = v := by
        simpa [j] using List.dropLast_append_getLast hvne
      have htailLen : u.length = v.dropLast.length := by
        simp only [List.length_dropLast]
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have hprefix : finiteSlotDecode S ω u =
          finiteSlotDecode S ω v.dropLast := by
        have hdecode' := hdecode
        rw [finiteSlotDecode_append_singleton S ω u i, ← hsplit,
          finiteSlotDecode_append_singleton S ω v.dropLast j] at hdecode'
        have h := congrArg (List.take u.length) hdecode'
        simpa [finiteSlotDecode_length, htailLen] using h
      have htail : u = v.dropLast := ih htailLen hprefix
      have hv : v = u ++ [j] := by
        rw [← hsplit, htail]
      have hslots :
          finiteSlotAddress S (ω (finiteSlotDecode S ω u)) i =
            finiteSlotAddress S (ω (finiteSlotDecode S ω u)) j := by
        have hdecode' := hdecode
        rw [finiteSlotDecode_append_singleton S ω u i, hv,
          finiteSlotDecode_append_singleton S ω u j] at hdecode'
        have h := List.append_cancel_left hdecode'
        simpa using h
      have hij : i = j := finiteSlotAddress_injective S
        (ω (finiteSlotDecode S ω u)) hslots
      rw [hv]
      simp [hij]

/-- The coded active address representing a source path in the selected
population is unique at each fixed generation. -/
lemma finiteSlotDecode_existsUnique_of_mem_population
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ)
    {p : TreeNode α} (hp : p ∈ StepSelection.population S n ω) :
    ∃! u : TreeNode (Fin 2), u.length = n ∧
      Combinatorics.Branching.surviveAlong
        (finiteSlotCodedStepField S ω) [] u ∧
      finiteSlotDecode S ω u = p := by
  obtain ⟨u, hlen, hactive, hdecode⟩ :=
    finiteSlotDecode_exists_of_mem_population S ω hcapacity n hp
  refine ⟨u, ⟨hlen, hactive, hdecode⟩, ?_⟩
  intro v hv
  apply finiteSlotDecode_injective_level S ω (by rw [hv.1, hlen])
  exact hv.2.2.trans hdecode.symm

/-- The source roots associated with every binary address at generation `n`.
There are finitely many such addresses, so the random family has countable
range even though its values depend on the already revealed field. -/
noncomputable def finiteSlotLevelRoots
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    (Fin n → Fin 2) → TreeNode α :=
  fun u => finiteSlotDecode S ω (List.ofFn u)

lemma finiteSlotLevelRoots_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    Measurable[generationFiltration (M := Step α X) n]
      (finiteSlotLevelRoots S · n) := by
  apply (@measurable_pi_iff
    (Mark α (Step α X)) (Fin n → Fin 2) (fun _ => TreeNode α)
    (generationFiltration (M := Step α X) n) (fun _ => inferInstance)
    (finiteSlotLevelRoots S · n)).2
  intro u
  change Measurable[generationFiltration (M := Step α X) n]
    (fun ω : Mark α (Step α X) => finiteSlotDecode S ω (List.ofFn u))
  have h := finiteSlotDecode_measurable S hS (List.ofFn u)
  rw [List.length_ofFn] at h
  exact h

lemma finiteSlotLevelRoots_range_countable
    {α X : Type*} [Countable α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (n : ℕ) :
    (Set.range (finiteSlotLevelRoots S · n)).Countable := by
  exact Set.to_countable _

lemma finiteSlotLevelRoots_fiber_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ)
    (roots : (Fin n → Fin 2) → TreeNode α) :
    MeasurableSet[generationFiltration (M := Step α X) n]
      {ω | finiteSlotLevelRoots S ω n = roots} := by
  have hchosen := finiteSlotLevelRoots_measurable S hS n
  have hcoord (u : Fin n → Fin 2) : Measurable[
      generationFiltration (M := Step α X) n]
      (fun ω => finiteSlotLevelRoots S ω n u) :=
    (measurable_pi_apply u).comp hchosen
  have hset : {ω : Mark α (Step α X) |
      finiteSlotLevelRoots S ω n = roots} =
      ⋂ u, {ω | finiteSlotLevelRoots S ω n u = roots u} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact funext_iff
  rw [hset]
  exact MeasurableSet.iInter fun u =>
    hcoord u (measurableSet_singleton (roots u))

lemma finiteSlotLevelRoots_depth
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (u : Fin n → Fin 2) :
    (finiteSlotLevelRoots S ω n u).length = n := by
  simp [finiteSlotLevelRoots, finiteSlotDecode_length]

lemma finiteSlotLevelRoots_injective
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    Function.Injective (finiteSlotLevelRoots S ω n) := by
  classical
  intro u v huv
  apply List.ofFn_injective
  exact finiteSlotDecode_injective_level S ω (by simp) (by
    simpa [finiteSlotLevelRoots] using huv)

/-- At every fixed generation, the full source subtrees below the decoded
binary addresses are independent fresh copies of the original step field.
The random address family is measurable from the past, has finite index, and
is pointwise injective. -/
lemma finiteSlotLevelSubtreeVector_law
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    (stepFieldLaw μ).map
      (selectedSubtreeStepFieldVector (finiteSlotLevelRoots S · n)) =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) => stepFieldLaw μ) := by
  classical
  exact selectedSubtreeStepFieldVector_law μ
    (finiteSlotLevelRoots S · n)
    (finiteSlotLevelRoots_measurable S hS n)
    (finiteSlotLevelRoots_range_countable S n)
    (finiteSlotLevelRoots_fiber_measurable S hS n)
    (fun ω u => finiteSlotLevelRoots_depth S ω n u)
    (fun ω => finiteSlotLevelRoots_injective S ω n)


end ProbabilityTheory.BranchingRandomWalk
