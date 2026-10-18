/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.BoundedOffspring
import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtreeVector
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Basic
import Probability.Independence.ConditionalIntegral

/-!
# Finite-slot coding of a bounded selected genealogy

A bounded selected family can be ranked by its slot order and represented by
an initial segment of `Fin 2`. This file develops the address coding needed
for comparing its actual descendants with a finite-slot Galton--Watson tree.
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

theorem finiteSlotSuccessor_gt
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

@[simp] theorem finiteSlotAddress_zero
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) :
    finiteSlotAddress S ξ 0 = firstSelectedSlot S ξ := by
  simp [finiteSlotAddress]

@[simp] theorem finiteSlotAddress_one
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) :
    finiteSlotAddress S ξ 1 =
      if 2 ≤ (S ξ).card then secondSelectedSlot S ξ else
        finiteSlotSuccessor (firstSelectedSlot S ξ) := by
  rfl

/-- Under the capacity-two bound, the two finite labels have distinct source
slots, including when the selected family is empty or a singleton. -/
theorem finiteSlotAddress_injective
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) :
    Function.Injective (finiteSlotAddress S ξ) := by
  classical
  have h01 : finiteSlotAddress S ξ 0 ≠ finiteSlotAddress S ξ 1 := by
    rw [finiteSlotAddress_zero, finiteSlotAddress_one]
    by_cases htwo : 2 ≤ (S ξ).card
    · rw [if_pos htwo]
      exact (secondSelectedSlot_mem_of_card S ξ htwo).2
    · rw [if_neg htwo]
      exact ne_of_lt (finiteSlotSuccessor_gt _)
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (h01 hij)
  · exact False.elim (h01 hij.symm)
  · rfl

/-- Every selected source slot is represented by an active binary label when
the selector keeps at most two children. -/
theorem finiteSlotAddress_exists_of_mem
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
    · rw [finiteSlotAddress_one, if_pos htwo, hsecond]

/-- A path belongs to the selected population exactly when each of its
successive slots is retained by the selector at its parent. -/
def selectedAlong {α X : Type*}
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    TreeNode α → TreeNode α → Prop
  | _, [] => True
  | v, i :: p => i ∈ S (ω v) ∧ selectedAlong S ω (v ++ [i]) p

theorem selectedAlong_append_singleton
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
theorem mem_population_iff_length_selectedAlong
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
theorem finiteSlotAddress_mem_iff
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
theorem finiteSlotAddress_measurable
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
@[simp] theorem finiteSlotDecode_append_singleton
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
theorem finiteSlotDecode_surviveAlong_iff_selectedAlong
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

theorem finiteSlotRank_address
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

theorem finiteSlotDecode_eq_decodeFrom
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (u : TreeNode (Fin 2)) :
    finiteSlotDecode S ω u = finiteSlotDecodeFrom S ω [] u := rfl

@[simp] theorem finiteSlotDecodeFrom_append_singleton
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (v : TreeNode α) (u : TreeNode (Fin 2)) (i : Fin 2) :
    finiteSlotDecodeFrom S ω v (u ++ [i]) =
      finiteSlotDecodeFrom S ω v u ++
        [finiteSlotAddress S (ω (finiteSlotDecodeFrom S ω v u)) i] := by
  simp [finiteSlotDecodeFrom, List.foldl_append]

theorem finiteSlotEncodeFrom_length
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) :
    ∀ (v p : TreeNode α),
      (finiteSlotEncodeFrom S ω v p).length = p.length := by
  intro v p
  induction p generalizing v with
  | nil => rfl
  | cons i p ih => simp [finiteSlotEncodeFrom, ih]

theorem finiteSlotDecodeFrom_encodeFrom
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
theorem finiteSlotDecode_length
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
theorem finiteSlotDecode_mem_population_of_surviveAlong
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
theorem finiteSlotDecode_exists_of_mem_population
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
theorem finiteSlotDecode_measurable
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
theorem finiteSlotDecode_injective_level
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
theorem finiteSlotDecode_existsUnique_of_mem_population
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

theorem finiteSlotLevelRoots_measurable
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

theorem finiteSlotLevelRoots_range_countable
    {α X : Type*} [Countable α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (n : ℕ) :
    (Set.range (finiteSlotLevelRoots S · n)).Countable := by
  exact Set.to_countable _

theorem finiteSlotLevelRoots_fiber_measurable
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
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact funext_iff
  rw [hset]
  exact MeasurableSet.iInter fun u =>
    hcoord u (measurableSet_singleton (roots u))

/-- The active coded parents at generation `n`. -/
noncomputable def finiteSlotActiveLabels
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    Finset (Fin n → Fin 2) :=
  by
    classical
    exact Finset.univ.filter fun u =>
      Combinatorics.Branching.surviveAlong
        (finiteSlotCodedStepField S ω) [] (List.ofFn u)

/-- The active finite-slot labels are in bijection with the source selected
population at the same generation. -/
theorem finiteSlotActiveLabels_card_eq_population_card
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    (finiteSlotActiveLabels S ω n).card =
      (StepSelection.population S n ω).card := by
  classical
  apply Finset.card_bij (fun u _ => finiteSlotLevelRoots S ω n u)
  · intro u hu
    have hactive := (Finset.mem_filter.mp hu).2
    have hlen : (List.ofFn u).length = n := by simp
    have hpop := finiteSlotDecode_mem_population_of_surviveAlong
      S ω hcapacity n hlen hactive
    simpa [finiteSlotLevelRoots] using hpop
  · intro u hu v hv huv
    apply List.ofFn_injective
    apply finiteSlotDecode_injective_level S ω (by simp)
    simpa [finiteSlotLevelRoots] using huv
  · intro p hp
    obtain ⟨u, ⟨hlen, hactive, hdecode⟩, _⟩ :=
      finiteSlotDecode_existsUnique_of_mem_population
        S ω hcapacity n hp
    let v : Fin n → Fin 2 :=
      fun i => u.get (Fin.cast hlen.symm i)
    have hvlist : List.ofFn v = u := by
      calc
        List.ofFn v = List.ofFn u.get := by
          symm
          exact List.ofFn_congr hlen u.get
        _ = u := List.ofFn_get u
    refine ⟨v, ?_, ?_⟩
    · simp only [finiteSlotActiveLabels, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hvlist]
      exact hactive
    · simpa [finiteSlotLevelRoots, hvlist] using hdecode

/-- Distinct parent addresses have disjoint child families, and the list
append map preserves the number of selected slots. Hence a growth step has
cardinality equal to the sum of its parent offspring counts. -/
theorem grow_card_eq_sum_childCount
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (parents : Finset (TreeNode α))
    (ω : Mark α (Step α X)) :
    (StepSelection.grow S parents ω).card =
      ∑ u ∈ parents, (S (ω u)).card := by
  have hchildren (u : TreeNode α) :
      (StepSelection.children S ω u).card = (S (ω u)).card := by
    have heq : StepSelection.children S ω u =
        (S (ω u)).image (fun i => u ++ [i]) := by
      ext q
      simp [StepSelection.children]
    rw [heq]
    apply Finset.card_image_iff.mpr
    intro i hi j hj hij
    have hsingle : [i] = [j] := List.append_cancel_left hij
    simpa using hsingle
  have hdisjoint :
      (parents : Set (TreeNode α)).PairwiseDisjoint
        (StepSelection.children S ω) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro u hu v hv hne
    obtain ⟨q, hq⟩ := hne
    have hqu : q ∈ StepSelection.children S ω u :=
      (Finset.mem_inter.mp hq).1
    have hqv : q ∈ StepSelection.children S ω v :=
      (Finset.mem_inter.mp hq).2
    obtain ⟨i, hi, hqi⟩ :=
      (StepSelection.mem_children_iff S ω u q).mp hqu
    obtain ⟨j, hj, hqj⟩ :=
      (StepSelection.mem_children_iff S ω v q).mp hqv
    have happend : u ++ [i] = v ++ [j] := hqi.symm.trans hqj
    have hdrop := congrArg List.dropLast happend
    simpa using hdrop
  have hgrow : StepSelection.grow S parents ω =
      parents.biUnion (StepSelection.children S ω) := by
    ext q
    simp [StepSelection.grow]
  calc
    (StepSelection.grow S parents ω).card =
        (parents.biUnion (StepSelection.children S ω)).card :=
      congrArg Finset.card hgrow
    _ = ∑ u ∈ parents, (StepSelection.children S ω u).card :=
      Finset.card_biUnion hdisjoint
    _ = ∑ u ∈ parents, (S (ω u)).card := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hchildren u

/-- The selected population cardinality advances by summing the selected
offspring counts of the current generation. -/
theorem population_card_succ_eq_sum_childCount
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    (StepSelection.population S (n + 1) ω).card =
      ∑ u ∈ StepSelection.population S n ω, (S (ω u)).card := by
  rw [StepSelection.population_succ,
    grow_card_eq_sum_childCount S _ (frontierMarks n ω)]
  apply Finset.sum_congr rfl
  intro u hu
  have hdepth := StepSelection.population_depth S ω n u hu
  simp [frontierMarks, hdepth]

/-- The coded active-parent set is observable from the source field through
generation `n`. Pathwise, its members are exactly the coded addresses of the
source N-selected population. -/
theorem finiteSlotActiveLabels_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    Measurable[generationFiltration (M := Step α X) n]
      (finiteSlotActiveLabels S · n) := by
  classical
  let F : MeasurableSpace (Mark α (Step α X)) :=
    generationFiltration (M := Step α X) n
  have hpopulation : Measurable[F] (StepSelection.population S n) :=
    StepSelection.population_adapted S hS n
  rw [measurable_finset_iff]
  intro u
  have hroot : Measurable[F] (fun ω : Mark α (Step α X) =>
      finiteSlotLevelRoots S ω n u) := by
    exact (measurable_pi_apply u).comp
      (finiteSlotLevelRoots_measurable S hS n)
  have hrel : Measurable (fun q :
      TreeNode α × Finset (TreeNode α) => q.1 ∈ q.2) :=
    measurable_of_countable _
  have hmem : Measurable[F] (fun ω : Mark α (Step α X) =>
      finiteSlotLevelRoots S ω n u ∈ StepSelection.population S n ω) :=
    hrel.comp (hroot.prodMk hpopulation)
  have hequiv : ∀ ω : Mark α (Step α X),
      u ∈ finiteSlotActiveLabels S ω n ↔
        finiteSlotLevelRoots S ω n u ∈ StepSelection.population S n ω := by
    intro ω
    simp only [finiteSlotActiveLabels, Finset.mem_filter, Finset.mem_univ,
      true_and]
    let p := finiteSlotDecode S ω (List.ofFn u)
    have hlength : p.length = n := by
      simp [p, finiteSlotLevelRoots, finiteSlotDecode_length]
    have hdecode : p = finiteSlotLevelRoots S ω n u := by
      rfl
    constructor
    · intro hactive
      change finiteSlotDecode S ω (List.ofFn u) ∈
        StepSelection.population S n ω
      exact finiteSlotDecode_mem_population_of_surviveAlong S ω hcapacity n
        (by simp) hactive
    · intro hp
      change p ∈ StepSelection.population S n ω at hp
      have hp' := (mem_population_iff_length_selectedAlong S ω n p).mp hp
      exact (finiteSlotDecode_surviveAlong_iff_selectedAlong S ω
        hcapacity (List.ofFn u)).mpr (by simpa [p] using hp'.2)
  have hfun : (fun ω : Mark α (Step α X) =>
      u ∈ finiteSlotActiveLabels S ω n) =
    (fun ω => finiteSlotLevelRoots S ω n u ∈
      StepSelection.population S n ω) := by
    funext ω
    exact propext (hequiv ω)
  rw [hfun]
  exact hmem

theorem finiteSlotLevelRoots_depth
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ)
    (u : Fin n → Fin 2) :
    (finiteSlotLevelRoots S ω n u).length = n := by
  simp [finiteSlotLevelRoots, finiteSlotDecode_length]

theorem finiteSlotLevelRoots_injective
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
theorem finiteSlotLevelSubtreeVector_law
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

/-- The finite-slot offspring observations at a fixed decoded generation are
independent and each has the offspring law induced by the selector. -/
noncomputable def finiteSlotLevelSteps
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X)) (n : ℕ) :
    (Fin n → Fin 2) → Step (Fin 2) PUnit.{1} :=
  fun u => finiteOffspringStep S (ω (finiteSlotLevelRoots S ω n u))

/-- Summing the coded offspring counts over active labels gives exactly the
sum of selected offspring counts over the source population. -/
theorem finiteSlotActiveLabels_sum_childCount_eq_population_sum
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    ∑ u ∈ finiteSlotActiveLabels S ω n,
        (finiteSlotLevelSteps S ω n u).childCount.toNat =
      ∑ p ∈ StepSelection.population S n ω, (S (ω p)).card := by
  classical
  have hactivePop {u : Fin n → Fin 2} :
      u ∈ finiteSlotActiveLabels S ω n ↔
        finiteSlotLevelRoots S ω n u ∈ StepSelection.population S n ω := by
    constructor
    · intro hu
      have hsurvive := (Finset.mem_filter.mp hu).2
      have hlen : (List.ofFn u).length = n := by simp
      have hp := finiteSlotDecode_mem_population_of_surviveAlong
        S ω hcapacity n hlen hsurvive
      simpa [finiteSlotLevelRoots] using hp
    · intro hp
      have hpop := (mem_population_iff_length_selectedAlong S ω n
        (finiteSlotLevelRoots S ω n u)).mp hp
      have hselected : selectedAlong S ω []
          (finiteSlotDecode S ω (List.ofFn u)) := by
        simpa [finiteSlotLevelRoots] using hpop.2
      have hsurvive :=
        (finiteSlotDecode_surviveAlong_iff_selectedAlong S ω hcapacity
          (List.ofFn u)).mpr hselected
      simp only [finiteSlotActiveLabels, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hsurvive
  apply Finset.sum_bij (fun u _ => finiteSlotLevelRoots S ω n u)
  · intro u hu
    exact hactivePop.mp hu
  · intro u hu v hv huv
    apply List.ofFn_injective
    apply finiteSlotDecode_injective_level S ω (by simp)
    simpa [finiteSlotLevelRoots] using huv
  · intro p hp
    obtain ⟨u, ⟨hlen, hsurvive, hdecode⟩, _⟩ :=
      finiteSlotDecode_existsUnique_of_mem_population
        S ω hcapacity n hp
    let v : Fin n → Fin 2 :=
      fun i => u.get (Fin.cast hlen.symm i)
    have hvlist : List.ofFn v = u := by
      calc
        List.ofFn v = List.ofFn u.get := by
          symm
          exact List.ofFn_congr hlen u.get
        _ = u := List.ofFn_get u
    refine ⟨v, ?_, ?_⟩
    · simp only [finiteSlotActiveLabels, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hvlist]
      exact hsurvive
    · simpa [finiteSlotLevelRoots, hvlist] using hdecode
  · intro u hu
    simp [finiteSlotLevelSteps, finiteOffspringStep_childCount,
      hcapacity (ω (finiteSlotLevelRoots S ω n u))]

/-- Pathwise finite-generation transition for the coded reserve population.
Each active source parent contributes its selected child count, and the
active-label cardinality agrees with the actual selected population. -/
theorem finiteSlotActiveLabels_card_succ_eq_sum
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    (finiteSlotActiveLabels S ω (n + 1)).card =
      ∑ u ∈ finiteSlotActiveLabels S ω n,
        (finiteSlotLevelSteps S ω n u).childCount.toNat := by
  calc
    (finiteSlotActiveLabels S ω (n + 1)).card =
        (StepSelection.population S (n + 1) ω).card :=
      finiteSlotActiveLabels_card_eq_population_card S ω hcapacity (n + 1)
    _ = ∑ p ∈ StepSelection.population S n ω, (S (ω p)).card :=
      population_card_succ_eq_sum_childCount S ω n
    _ = ∑ u ∈ finiteSlotActiveLabels S ω n,
        (finiteSlotLevelSteps S ω n u).childCount.toNat :=
      (finiteSlotActiveLabels_sum_childCount_eq_population_sum
        S ω hcapacity n).symm

/-- The offspring sum generated from a fixed active-label set by a row of
finite-slot offspring configurations. -/
noncomputable def finiteSlotRowCountSum
    (n : ℕ)
    (p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1})) : ℝ :=
  ∑ u : Fin n → Fin 2,
    if u ∈ p.1 then ((p.2 u).childCount.toNat : ℝ) else 0

theorem finiteSlotRowCountSum_measurable (n : ℕ) :
    Measurable (finiteSlotRowCountSum n) := by
  classical
  unfold finiteSlotRowCountSum
  apply Finset.measurable_fun_sum Finset.univ
  intro u hu
  have hmem : Measurable (fun p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) => u ∈ p.1) :=
    (measurable_finset_mem u).comp measurable_fst
  have hset : MeasurableSet {p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) | u ∈ p.1} :=
    measurableSet_setOfPred.mpr hmem
  have hcount : Measurable (fun p : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) =>
      ((p.2 u).childCount.toNat : ℝ)) := by
    have hcast : Measurable (fun z : ℕ∞ => (z.toNat : ℝ)) :=
      measurable_of_countable _
    exact hcast.comp <| Step.childCount_measurable.comp <|
      (measurable_pi_apply u).comp measurable_snd
  exact Measurable.ite hset hcount measurable_const

theorem finiteSlotRowCountSum_eq_sum
    (n : ℕ) (A : Finset (Fin n → Fin 2))
    (rows : (Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :
    finiteSlotRowCountSum n (A, rows) =
      ∑ u ∈ A, ((rows u).childCount.toNat : ℝ) := by
  classical
  simp [finiteSlotRowCountSum, Finset.sum_ite_mem_eq]

theorem finiteSlotLevelSteps_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    Measurable (finiteSlotLevelSteps S · n) := by
  classical
  let roots : Mark α (Step α X) → (Fin n → Fin 2) → TreeNode α :=
    fun ω => finiteSlotLevelRoots S ω n
  let vector := selectedSubtreeStepFieldVector roots
  let observe : StepField α X → Step (Fin 2) PUnit.{1} :=
    fun field => finiteOffspringStep S (field [])
  let observeVector :
      ((Fin n → Fin 2) → StepField α X) →
        ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :=
    fun fields u => observe (fields u)
  have hvector : Measurable vector :=
    selectedSubtreeStepFieldVector_measurable roots
      (finiteSlotLevelRoots_measurable S hS n)
      (finiteSlotLevelRoots_range_countable S n)
  have hobserve : Measurable observe := by
    exact (finiteOffspringStep_measurable S hS).comp
      (measurable_pi_apply ([] : TreeNode α))
  have hobserveVector : Measurable observeVector := by
    apply measurable_pi_iff.mpr
    intro u
    exact hobserve.comp (measurable_pi_apply u)
  have hcompose : (finiteSlotLevelSteps S · n) = observeVector ∘ vector := by
    funext ω u
    simp [finiteSlotLevelSteps, observe, observeVector, vector, roots,
      selectedSubtreeStepFieldVector, subtreeStepFieldVector, subtreeStepField]
  rw [hcompose]
  exact hobserveVector.comp hvector

theorem finiteSlotLevelSteps_law
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    (stepFieldLaw μ).map (finiteSlotLevelSteps S · n) =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
          S hS :
          Measure (Step (Fin 2) PUnit.{1}))) := by
  classical
  let roots : Mark α (Step α X) → (Fin n → Fin 2) → TreeNode α :=
    fun ω => finiteSlotLevelRoots S ω n
  let vector := selectedSubtreeStepFieldVector roots
  let ν : ProbabilityMeasure (Step α X) := ⟨μ, inferInstance⟩
  let observe : StepField α X → Step (Fin 2) PUnit.{1} :=
    fun field => finiteOffspringStep S (field [])
  let observeVector :
      ((Fin n → Fin 2) → StepField α X) →
        ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :=
    fun fields u => observe (fields u)
  have hobserve : Measurable observe := by
    exact (finiteOffspringStep_measurable S hS).comp
      (measurable_pi_apply ([] : TreeNode α))
  have hmap : Measure.map observe (stepFieldLaw μ) =
      (finiteOffspringLaw ν S hS :
        Measure (Step (Fin 2) PUnit.{1})) := by
    change Measure.map (fun field : StepField α X =>
      finiteOffspringStep S (field ([] : TreeNode α))) (stepFieldLaw μ) = _
    rw [show (fun field : StepField α X =>
        finiteOffspringStep S (field ([] : TreeNode α))) =
        (finiteOffspringStep S) ∘ (fun field : StepField α X =>
          field ([] : TreeNode α)) by rfl]
    rw [← Measure.map_map (finiteOffspringStep_measurable S hS)
      (measurable_pi_apply ([] : TreeNode α))]
    rw [stepFieldLaw_coordinate μ []]
    rfl
  have hvector : (stepFieldLaw μ).map vector =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) => stepFieldLaw μ) := by
    exact finiteSlotLevelSubtreeVector_law μ S hS n
  have hmapVector :
      (Measure.infinitePi (fun _ : (Fin n → Fin 2) => stepFieldLaw μ)).map
          observeVector =
        Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
          Measure.map observe (stepFieldLaw μ)) := by
    exact Measure.infinitePi_map_pi
      (μ := fun _ : (Fin n → Fin 2) => stepFieldLaw μ)
      (f := fun _ => observe) (hf := fun _ => hobserve)
  have hvectorMeasurable : Measurable vector :=
    selectedSubtreeStepFieldVector_measurable roots
      (finiteSlotLevelRoots_measurable S hS n)
      (finiteSlotLevelRoots_range_countable S n)
  have hmapVectorMeasurable : Measurable
      observeVector := by
    apply measurable_pi_iff.mpr
    intro u
    exact hobserve.comp (measurable_pi_apply u)
  have hcompose : (fun ω => finiteSlotLevelSteps S ω n) =
      observeVector ∘ vector := by
    funext ω u
    simp [finiteSlotLevelSteps, observe, observeVector, vector, roots,
      selectedSubtreeStepFieldVector, subtreeStepFieldVector, subtreeStepField]
  calc
    (stepFieldLaw μ).map (finiteSlotLevelSteps S · n) =
        (Measure.infinitePi (fun _ : (Fin n → Fin 2) => stepFieldLaw μ)).map
          observeVector := by
      rw [hcompose, ← Measure.map_map hmapVectorMeasurable hvectorMeasurable,
        hvector]
    _ = Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        Measure.map observe (stepFieldLaw μ)) := hmapVector
    _ = Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        (finiteOffspringLaw ν S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
      apply Measure.eq_infinitePi
      intro t A hA
      rw [Measure.infinitePi_pi _ (fun i _ => hA i)]
      apply Finset.prod_congr rfl
      intro i hi
      exact congrArg (fun ν : Measure (Step (Fin 2) PUnit.{1}) => ν (A i)) hmap

/-- The decoded offspring family at generation `n` is independent of the
source marks revealed before that generation. -/
theorem finiteSlotLevelSteps_independent
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) (n : ℕ) :
    Indep (generationFiltration (M := Step α X) n)
      (MeasurableSpace.comap (finiteSlotLevelSteps S · n) inferInstance)
      (stepFieldLaw μ) := by
  classical
  let roots : Mark α (Step α X) → (Fin n → Fin 2) → TreeNode α :=
    fun ω => finiteSlotLevelRoots S ω n
  let vector := selectedSubtreeStepFieldVector roots
  let observe : StepField α X → Step (Fin 2) PUnit.{1} :=
    fun field => finiteOffspringStep S (field [])
  let observeVector :
      ((Fin n → Fin 2) → StepField α X) →
        ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) :=
    fun fields u => observe (fields u)
  have hchosen := finiteSlotLevelRoots_measurable S hS n
  have hind := selectedSubtreeStepFieldVector_independent μ roots
    hchosen (finiteSlotLevelRoots_range_countable S n)
    (finiteSlotLevelRoots_fiber_measurable S hS n)
    (fun ω u => finiteSlotLevelRoots_depth S ω n u)
    (fun ω => finiteSlotLevelRoots_injective S ω n)
  have hobserve : Measurable observe := by
    exact (finiteOffspringStep_measurable S hS).comp
      (measurable_pi_apply ([] : TreeNode α))
  have hobserveVector : Measurable observeVector := by
    apply measurable_pi_iff.mpr
    intro u
    exact hobserve.comp (measurable_pi_apply u)
  have hcompose : (finiteSlotLevelSteps S · n) = observeVector ∘ vector := by
    funext ω u
    simp [finiteSlotLevelSteps, observe, observeVector, vector, roots,
      selectedSubtreeStepFieldVector, subtreeStepFieldVector, subtreeStepField]
  apply indep_of_indep_of_le_right hind
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    observeVector hobserveVector hcompose

theorem finiteSlotActiveLabels_levelSteps_independent
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    IndepFun (finiteSlotActiveLabels S · n)
      (finiteSlotLevelSteps S · n) (stepFieldLaw μ) := by
  classical
  have hactive : Measurable[generationFiltration (M := Step α X) n]
      (finiteSlotActiveLabels S · n) :=
    finiteSlotActiveLabels_measurable S hS hcapacity n
  have hsteps : Measurable (finiteSlotLevelSteps S · n) :=
    finiteSlotLevelSteps_measurable S hS n
  have hind := finiteSlotLevelSteps_independent μ S hS n
  have hsmall : Indep
      (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (MeasurableSpace.comap (finiteSlotLevelSteps S · n) inferInstance)
      (stepFieldLaw μ) :=
    ProbabilityTheory.indep_of_indep_of_le_left hind hactive.comap_le
  rw [IndepFun_iff_Indep]
  exact hsmall

/-- The observable active set and the fresh offspring row have a product
joint law. Thus finite-horizon moment recurrences can condition on the active
set without a stopping-time theorem. -/
theorem finiteSlotActiveLabels_levelSteps_jointLaw
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    (stepFieldLaw μ).map (fun ω =>
      (finiteSlotActiveLabels S ω n, finiteSlotLevelSteps S ω n)) =
      ((stepFieldLaw μ).map (finiteSlotActiveLabels S · n)).prod
        (Measure.infinitePi fun _ : (Fin n → Fin 2) =>
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
            S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
  have hactive : Measurable (finiteSlotActiveLabels S · n) :=
    (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
      (generationFiltration (M := Step α X) |>.le n) le_rfl
  have hsteps : Measurable (finiteSlotLevelSteps S · n) :=
    finiteSlotLevelSteps_measurable S hS n
  have hind := finiteSlotActiveLabels_levelSteps_independent
    μ S hS hcapacity n
  rw [hind.map_prod_eq_prod_map_map hactive.aemeasurable hsteps.aemeasurable,
    finiteSlotLevelSteps_law μ S hS n]

/-- Conditional first-moment recursion at an observable generation: after
conditioning on the active labels, integrate their fresh offspring counts
against the fixed iid finite-slot row law. -/
theorem finiteSlotActiveLabels_condExp_succ_card
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) (n : ℕ) :
    condExp (MeasurableSpace.comap (finiteSlotActiveLabels S · n) inferInstance)
      (stepFieldLaw μ)
      (fun ω => ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ)) =ᵐ[stepFieldLaw μ]
    fun ω => ∫ row, finiteSlotRowCountSum n
      (finiteSlotActiveLabels S ω n, row) ∂
        Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
            S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
  classical
  let active : Mark α (Step α X) → Finset (Fin n → Fin 2) :=
    fun ω => finiteSlotActiveLabels S ω n
  let rows : Mark α (Step α X) →
      (Fin n → Fin 2) → Step (Fin 2) PUnit.{1} :=
    fun ω => finiteSlotLevelSteps S ω n
  let nextSize : Mark α (Step α X) → ℝ := fun ω =>
    ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ)
  let rowSum : Finset (Fin n → Fin 2) ×
      ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) → ℝ :=
    finiteSlotRowCountSum n
  have hactive : Measurable active := by
    simpa [active] using
      (finiteSlotActiveLabels_measurable S hS hcapacity n).mono
        (generationFiltration (M := Step α X) |>.le n) le_rfl
  have hrows : Measurable rows := by
    simpa [rows] using finiteSlotLevelSteps_measurable S hS n
  have hind := finiteSlotActiveLabels_levelSteps_independent
    μ S hS hcapacity n
  have hnext : Measurable nextSize := by
    change Measurable (fun ω =>
      ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ))
    exact (measurable_of_countable fun A : Finset (Fin (n + 1) → Fin 2) =>
      (A.card : ℝ)).comp <|
        (finiteSlotActiveLabels_measurable S hS hcapacity (n + 1)).mono
          (generationFiltration (M := Step α X) |>.le (n + 1)) le_rfl
  have hnextBound : ∀ ω, ‖nextSize ω‖ ≤ (2 ^ (n + 1) : ℝ) := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hcard : (finiteSlotActiveLabels S ω (n + 1)).card ≤ 2 ^ (n + 1) := by
      rw [finiteSlotActiveLabels_card_eq_population_card S ω hcapacity]
      exact StepSelection.population_card_le S 2 hcapacity ω (n + 1)
    have hreal :
        ((finiteSlotActiveLabels S ω (n + 1)).card : ℝ) ≤
          (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast hcard
    simpa only [nextSize] using hreal
  have hnextIntegrable : Integrable nextSize (stepFieldLaw μ) :=
    Integrable.of_bound hnext.aestronglyMeasurable (2 ^ (n + 1) : ℝ)
      (ae_of_all _ hnextBound)
  have hrowMeasurable : Measurable rowSum := by
    exact finiteSlotRowCountSum_measurable n
  have hrowStrong : StronglyMeasurable rowSum := hrowMeasurable.stronglyMeasurable
  have hsample : (fun ω => rowSum (active ω, rows ω)) = nextSize := by
    funext ω
    have hsum := finiteSlotActiveLabels_card_succ_eq_sum S ω hcapacity n
    change finiteSlotRowCountSum n
      (finiteSlotActiveLabels S ω n, finiteSlotLevelSteps S ω n) = _
    rw [finiteSlotRowCountSum_eq_sum]
    simpa only [Nat.cast_sum] using
      congrArg (fun k : ℕ => (k : ℝ)) hsum.symm
  have hsampleIntegrable :
      Integrable (fun ω => rowSum (active ω, rows ω)) (stepFieldLaw μ) := by
    rw [hsample]
    exact hnextIntegrable
  letI : MeasurableSingletonClass (Option PUnit.{1}) := by
    refine ⟨fun x => ?_⟩
    cases x with
    | none => exact measurableSet_option_none
    | some x =>
      rw [show ({some x} : Set (Option PUnit.{1})) = some '' {x} by
        ext y
        simp]
      exact measurableSet_option_some_image (measurableSet_singleton x)
  letI : MeasurableSingletonClass (Step (Fin 2) PUnit.{1}) := inferInstance
  letI : StandardBorelSpace (Step (Fin 2) PUnit.{1}) := by infer_instance
  letI : StandardBorelSpace ((Fin n → Fin 2) → Step (Fin 2) PUnit.{1}) := by
    infer_instance
  have hcond := hind.condExp_prod_ae_eq_integral_map
    hactive hrows hrowStrong hsampleIntegrable
  rw [hsample] at hcond
  have hrowLaw : (stepFieldLaw μ).map rows =
      Measure.infinitePi (fun _ : (Fin n → Fin 2) =>
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
          S hS : Measure (Step (Fin 2) PUnit.{1}))) := by
    simpa [rows] using finiteSlotLevelSteps_law μ S hS n
  rw [hrowLaw] at hcond
  simpa [active, nextSize, rowSum] using hcond

end ProbabilityTheory.BranchingRandomWalk
