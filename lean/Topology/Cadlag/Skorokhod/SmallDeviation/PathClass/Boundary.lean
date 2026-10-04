/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.UnitInterval

/-!
# Finite step boundaries for path classes

A `StepBoundary` is a finite right-continuous step function on `[0,1]` with
values in the extended reals. Finite values and either infinite side are
represented directly. Knots at both endpoints are allowed except at zero,
where the right-hand level is the only boundary value. The totalized left and
right traces record the available one-sided levels at every time.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- A finite right-continuous step boundary on `[0,1]`, with values in the
extended real line. At a knot the new level is used. Knots at both endpoints
are allowed except at zero, where there is no interval to its left. -/
structure StepBoundary where
  knots : Finset unitInterval
  noBotKnot : ⊥ ∉ knots
  levels : Fin (knots.card + 1) → EReal

namespace StepBoundary

/-- A constant boundary. -/
def constant (v : EReal) : StepBoundary :=
  ⟨∅, by simp, fun _ => v⟩

/-- A boundary with one jump at a nonzero time. -/
def singleJump (t : unitInterval) (ht : t ≠ ⊥) (before after : EReal) :
    StepBoundary :=
  ⟨{t}, by simpa using ht.symm, fun i => if i.val = 0 then before else after⟩

/-- The level index is the number of knots already reached. -/
noncomputable def levelIndex (b : StepBoundary) (t : unitInterval) : Fin (b.knots.card + 1) :=
  ⟨(b.knots.filter fun s => s ≤ t).card,
    Nat.lt_succ_of_le <| Finset.card_le_card (Finset.filter_subset _ _)⟩

/-- The index of the level immediately to the left of `t`. At the left
endpoint there is no left-hand interval, so we use the endpoint level. -/
noncomputable def leftLevelIndex (b : StepBoundary) (t : unitInterval) :
    Fin (b.knots.card + 1) :=
  if t = ⊥ then b.levelIndex t else
    ⟨(b.knots.filter fun s => s < t).card,
      Nat.lt_succ_of_le <| Finset.card_le_card (Finset.filter_subset _ _)⟩

/-- Evaluate the step boundary at time `t`. -/
noncomputable def eval (b : StepBoundary) (t : unitInterval) : EReal :=
  b.levels (b.levelIndex t)

/-- The right trace of a boundary. Right continuity means this is also its
value at every time. -/
noncomputable def rightTrace (b : StepBoundary) (t : unitInterval) : EReal :=
  b.eval t

/-- The left trace of a boundary. At time zero, where there is no left-hand
time interval, it is totalized by the value at zero. -/
noncomputable def leftTrace (b : StepBoundary) (t : unitInterval) : EReal :=
  b.levels (b.leftLevelIndex t)

@[simp]
theorem levelIndex_bot (b : StepBoundary) : b.levelIndex ⊥ = 0 := by
  have hfilter : b.knots.filter (fun s => s ≤ ⊥) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hle
    have hEq : s = ⊥ := le_antisymm hle bot_le
    have hsBot : (⊥ : unitInterval) ∈ b.knots := by simpa [hEq] using hs
    exact b.noBotKnot hsBot
  apply Fin.ext
  change (b.knots.filter (fun s => s ≤ ⊥)).card = 0
  rw [hfilter]
  simp

@[simp]
theorem levelIndex_top (b : StepBoundary) :
    b.levelIndex ⊤ = ⟨b.knots.card, Nat.lt_succ_self _⟩ := by
  apply Fin.ext
  simp [levelIndex]

@[simp]
theorem rightTrace_eq_eval (b : StepBoundary) (t : unitInterval) :
    b.rightTrace t = b.eval t := rfl

@[simp]
theorem rightTrace_top (b : StepBoundary) :
    b.rightTrace ⊤ = b.levels ⟨b.knots.card, Nat.lt_succ_self _⟩ := by
  simp [rightTrace, eval]

@[simp]
theorem leftLevelIndex_bot (b : StepBoundary) :
    b.leftLevelIndex ⊥ = b.levelIndex ⊥ := by
  simp [leftLevelIndex]

@[simp]
theorem leftTrace_bot (b : StepBoundary) :
    b.leftTrace ⊥ = b.eval ⊥ := by
  simp [leftTrace, eval]

theorem leftLevelIndex_eq_levelIndex_of_not_mem (b : StepBoundary)
    {t : unitInterval} (ht : t ∉ b.knots) :
    b.leftLevelIndex t = b.levelIndex t := by
  by_cases hbot : t = ⊥
  · simp [leftLevelIndex, hbot]
  · simp only [leftLevelIndex, hbot, ite_false]
    apply Fin.ext
    apply congrArg Finset.card
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hst⟩
      exact ⟨hs, le_of_lt hst⟩
    · rintro ⟨hs, hst⟩
      refine ⟨hs, ?_⟩
      by_contra hnotlt
      have hEq : s = t := le_antisymm hst (le_of_not_gt hnotlt)
      exact ht (hEq ▸ hs)

theorem leftTrace_eq_rightTrace_of_not_mem (b : StepBoundary)
    {t : unitInterval} (ht : t ∉ b.knots) :
    b.leftTrace t = b.rightTrace t := by
  simp [leftTrace, rightTrace, eval,
    leftLevelIndex_eq_levelIndex_of_not_mem b ht]

/-- Immediately to the left of a time, a finite step boundary agrees with its
left trace. The point `p` is chosen after every knot strictly before `t`. -/
theorem eval_eq_leftTrace_of_between (b : StepBoundary) {p s t : unitInterval}
    (hps : p < s) (hst : s < t)
    (hp : ∀ q ∈ b.knots, q < t → q ≤ p) :
    b.eval s = b.leftTrace t := by
  have htbot : t ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hst)
  change b.levels (b.levelIndex s) = b.levels (b.leftLevelIndex t)
  apply congrArg b.levels
  unfold leftLevelIndex
  rw [ite_eq_right htbot]
  unfold levelIndex
  apply Fin.ext
  change (b.knots.filter (fun q => q ≤ s)).card =
    (b.knots.filter (fun q => q < t)).card
  congr 1
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hqs⟩
    exact ⟨hq, lt_of_le_of_lt hqs hst⟩
  · rintro ⟨hq, hqt⟩
    exact ⟨hq, le_of_lt (lt_of_le_of_lt (hp q hq hqt) hps)⟩

/-- A finite knot set has a last knot strictly before any fixed positive time,
with the left endpoint used when there are no such knots. -/
theorem exists_left_gap_finset (knots : Finset unitInterval)
    {t : unitInterval} (ht : ⊥ < t) :
    ∃ p, p < t ∧ ∀ q ∈ knots, q < t → q ≤ p := by
  classical
  let prior := knots.filter fun q => q < t
  let candidates := insert (⊥ : unitInterval) prior
  have hne : candidates.Nonempty := ⟨⊥, Finset.mem_insert_self _ _⟩
  let p := candidates.max' hne
  have hpmem : p ∈ candidates := Finset.max'_mem _ _
  have hpt : p < t := by
    rcases Finset.mem_insert.mp hpmem with hp | hp
    · simpa [hp] using ht
    · have hp' : p ∈ prior := hp
      have hp'' : p < t := (Finset.mem_filter.mp hp').2
      exact hp''
  refine ⟨p, hpt, ?_⟩
  intro q hq hqt
  have hqprior : q ∈ prior := Finset.mem_filter.mpr ⟨hq, hqt⟩
  have hqcan : q ∈ candidates := Finset.mem_insert_of_mem hqprior
  exact Finset.le_max' _ _ hqcan

theorem exists_left_gap (b : StepBoundary) {t : unitInterval} (ht : ⊥ < t) :
    ∃ p, p < t ∧ ∀ q ∈ b.knots, q < t → q ≤ p :=
  exists_left_gap_finset b.knots ht

/-- A finite knot set has a first knot strictly after a fixed time, with the
right endpoint used when there are no later knots. -/
theorem exists_right_gap_finset (knots : Finset unitInterval)
    {t : unitInterval} (ht : t < ⊤) :
    ∃ q, t < q ∧ ∀ r ∈ knots, t < r → q ≤ r := by
  classical
  let later := knots.filter fun r => t < r
  let candidates := insert (⊤ : unitInterval) later
  have hne : candidates.Nonempty := ⟨⊤, Finset.mem_insert_self _ _⟩
  let q := candidates.min' hne
  have hqmem : q ∈ candidates := Finset.min'_mem _ _
  have htq : t < q := by
    rcases Finset.mem_insert.mp hqmem with htop | hlater
    · simpa [htop] using ht
    · have hq' : q ∈ later := hlater
      exact (Finset.mem_filter.mp hq').2
  refine ⟨q, htq, ?_⟩
  intro r hr htr
  have hrlater : r ∈ later := Finset.mem_filter.mpr ⟨hr, htr⟩
  have hrcandidate : r ∈ candidates := Finset.mem_insert_of_mem hrlater
  exact Finset.min'_le _ _ hrcandidate

theorem exists_right_gap (b : StepBoundary) {t : unitInterval} (ht : t < ⊤) :
    ∃ q, t < q ∧ ∀ r ∈ b.knots, t < r → q ≤ r :=
  exists_right_gap_finset b.knots ht

/-- Between consecutive knots, a finite-step boundary already has its value
at the left endpoint. -/
theorem eval_eq_rightTrace_of_between (b : StepBoundary) {t s q : unitInterval}
    (hts : t < s) (hsq : s < q)
    (hq : ∀ r ∈ b.knots, t < r → q ≤ r) :
    b.eval s = b.rightTrace t := by
  have hidx : b.levelIndex s = b.levelIndex t := by
    apply Fin.ext
    unfold levelIndex
    apply congrArg Finset.card
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, hrs⟩
      by_cases hrt : r ≤ t
      · exact ⟨hr, hrt⟩
      · have htr : t < r := lt_of_not_ge hrt
        have hqr := hq r hr htr
        exact False.elim (not_lt_of_ge (hqr.trans hrs) hsq)
    · rintro ⟨hr, hrt⟩
      exact ⟨hr, hrt.trans (le_of_lt hts)⟩
  rw [rightTrace_eq_eval]
  change b.levels (b.levelIndex s) = b.levels (b.levelIndex t)
  rw [hidx]

private theorem card_filter_eq_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.filter_insert]
    by_cases hp : p a
    · rw [ite_eq_left hp, Finset.card_insert_of_notMem]
      · rw [Finset.sum_insert ha, ih]
        simp [hp, Nat.add_comm]
      · intro h
        exact ha (Finset.mem_filter.mp h).1
    · rw [ite_eq_right hp, Finset.sum_insert ha, ih]
      simp [hp]

private theorem card_le_measurable (b : StepBoundary) :
    Measurable (fun t : unitInterval => (b.knots.filter (fun s => s ≤ t)).card) := by
  have hsum : Measurable (fun t : unitInterval =>
      ∑ q ∈ b.knots, if q ≤ t then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro q hq
    exact Measurable.ite (measurableSet_Ici : MeasurableSet (Set.Ici q))
      measurable_const measurable_const
  have hEq : (fun t : unitInterval => (b.knots.filter (fun s => s ≤ t)).card) =
      fun t => ∑ q ∈ b.knots, if q ≤ t then (1 : ℕ) else 0 := by
    funext t
    exact card_filter_eq_sum b.knots (fun s => s ≤ t)
  rw [hEq]
  exact hsum

private theorem card_lt_measurable (b : StepBoundary) :
    Measurable (fun t : unitInterval => (b.knots.filter (fun s => s < t)).card) := by
  have hsum : Measurable (fun t : unitInterval =>
      ∑ q ∈ b.knots, if q < t then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro q hq
    exact Measurable.ite (measurableSet_Ioi : MeasurableSet (Set.Ioi q))
      measurable_const measurable_const
  have hEq : (fun t : unitInterval => (b.knots.filter (fun s => s < t)).card) =
      fun t => ∑ q ∈ b.knots, if q < t then (1 : ℕ) else 0 := by
    funext t
    exact card_filter_eq_sum b.knots (fun s => s < t)
  rw [hEq]
  exact hsum

/-- The right-continuous level index of a finite-step boundary is measurable.
This follows by expressing the number of knots already reached as a finite
sum of measurable indicators. -/
theorem levelIndex_measurable (b : StepBoundary) : Measurable b.levelIndex := by
  have hbound (t : unitInterval) :
      (b.knots.filter (fun s => s ≤ t)).card < b.knots.card + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))
  let f : unitInterval → {n : ℕ // n < b.knots.card + 1} :=
    fun t => ⟨(b.knots.filter (fun s => s ≤ t)).card, hbound t⟩
  have hf : Measurable f := by
    unfold f
    exact (card_le_measurable b).subtype_mk
      (p := fun n : ℕ => n < b.knots.card + 1) (h := hbound)
  have hEq : b.levelIndex = Fin.equivSubtype.symm ∘ f := by
    funext t
    apply Fin.ext
    rfl
  rw [hEq]
  exact (measurable_of_finite Fin.equivSubtype.symm).comp hf

/-- The left-trace level index of a finite-step boundary is measurable. -/
theorem leftLevelIndex_measurable (b : StepBoundary) :
    Measurable b.leftLevelIndex := by
  have hbound (t : unitInterval) :
      (b.knots.filter (fun s => s < t)).card < b.knots.card + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))
  let f : unitInterval → {n : ℕ // n < b.knots.card + 1} :=
    fun t => ⟨(b.knots.filter (fun s => s < t)).card, hbound t⟩
  have hf : Measurable f := by
    unfold f
    exact (card_lt_measurable b).subtype_mk
      (p := fun n : ℕ => n < b.knots.card + 1) (h := hbound)
  have hraw : Measurable (fun t : unitInterval => Fin.equivSubtype.symm (f t)) :=
    (measurable_of_finite Fin.equivSubtype.symm).comp hf
  have hset : MeasurableSet {t : unitInterval | t = ⊥} := measurableSet_singleton ⊥
  unfold StepBoundary.leftLevelIndex
  exact Measurable.ite hset (levelIndex_measurable b) hraw

/-- Evaluation of a finite-step boundary is measurable. -/
theorem eval_measurable (b : StepBoundary) : Measurable b.eval := by
  exact (measurable_of_finite b.levels).comp b.levelIndex_measurable

/-- The totalized left-trace function of a finite-step boundary is measurable. -/
theorem leftTrace_measurable (b : StepBoundary) : Measurable b.leftTrace := by
  exact (measurable_of_finite b.levels).comp b.leftLevelIndex_measurable

@[simp]
theorem leftTrace_top_of_not_mem (b : StepBoundary)
    (ht : ⊤ ∉ b.knots) : b.leftTrace ⊤ = b.eval ⊤ := by
  exact leftTrace_eq_rightTrace_of_not_mem b ht

/-- At a terminal knot, the left trace is the preceding level. -/
theorem leftTrace_top (b : StepBoundary) (ht : ⊤ ∈ b.knots) :
    b.leftTrace ⊤ = b.levels ⟨b.knots.card - 1, by
      have hcard : 0 < b.knots.card := Finset.card_pos.mpr ⟨⊤, ht⟩
      omega⟩ := by
  have hnotbot : (⊤ : unitInterval) ≠ ⊥ := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num at hval
  have hfilter : b.knots.filter (fun s => s < ⊤) = b.knots.erase ⊤ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hs, hlt⟩
      exact ⟨by simpa using hlt.ne, hs⟩
    · rintro ⟨hne, hs⟩
      exact ⟨hs, lt_top_iff_ne_top.mpr hne⟩
  have hcard : (b.knots.filter (fun s => s < ⊤)).card = b.knots.card - 1 := by
    rw [hfilter, Finset.card_erase_of_mem ht]
  simp [leftTrace, leftLevelIndex, hnotbot, hcard]

@[simp]
theorem eval_empty (v : EReal) (t : unitInterval) :
    (⟨∅, by simp, fun _ => v⟩ : StepBoundary).eval t = v := by
  simp [eval]

@[simp]
theorem eval_constant (v : EReal) (t : unitInterval) :
    (constant v).eval t = v := by
  simp [constant, eval]

@[simp]
theorem leftTrace_constant (v : EReal) (t : unitInterval) :
    (constant v).leftTrace t = v := by
  simp [constant, leftTrace, leftLevelIndex]

@[simp]
theorem rightTrace_constant (v : EReal) (t : unitInterval) :
    (constant v).rightTrace t = v := by
  simp [constant, rightTrace, eval]

theorem leftTrace_singleJump (t : unitInterval) (ht : t ≠ ⊥)
    (before after : EReal) :
    (singleJump t ht before after).leftTrace t = before := by
  simp [singleJump, leftTrace, leftLevelIndex, ht,
    Finset.filter_singleton, Finset.card_singleton]

theorem rightTrace_singleJump (t : unitInterval) (ht : t ≠ ⊥)
    (before after : EReal) :
    (singleJump t ht before after).rightTrace t = after := by
  simp [singleJump, rightTrace, eval, levelIndex,
    Finset.filter_singleton, Finset.card_singleton]

/-- Before a single jump, a right-continuous step boundary retains its initial
level. -/
theorem eval_singleJump_of_lt (q : unitInterval) (hq : q ≠ ⊥)
    {s : unitInterval} (hsq : s < q) (before after : EReal) :
    (singleJump q hq before after).eval s = before := by
  by_cases hs : s = ⊥
  · subst s
    simp [singleJump, eval]
  · have hsbot : ⊥ < s := bot_lt_iff_ne_bot.mpr hs
    have hconst := eval_eq_rightTrace_of_between (singleJump q hq before after)
      hsbot hsq (fun r hr hqr => by
        rcases Finset.mem_singleton.mp hr with rfl
        exact le_rfl)
    rw [hconst, rightTrace_eq_eval]
    simp [singleJump, eval]

/-- After a single jump, a right-continuous step boundary uses its post-jump
level. -/
theorem eval_singleJump_of_le (q : unitInterval) (hq : q ≠ ⊥)
    {s : unitInterval} (hqs : q ≤ s) (before after : EReal) :
    (singleJump q hq before after).eval s = after := by
  classical
  simp [singleJump, eval, levelIndex, hqs]

end StepBoundary

end ProbabilityTheory.RandomWalk.Mogulskii
