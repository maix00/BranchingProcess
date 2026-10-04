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
public import Topology.Cadlag.Skorokhod.ContinuousMap
public import Topology.Cadlag.Skorokhod.Corridor

/-!
# Mogul'skii path classes `M₁` and `M₂`

This is the statement layer from §1 of Mogul'skii's paper. A boundary is a
finite right-continuous step function with values in the extended reals, so
unbounded sides of a corridor are represented rather than silently replaced
by finite real bounds. Knots at either endpoint are handled by explicit
one-sided traces, with the missing trace at an endpoint totalized by the
endpoint value. `M₂` is defined by the source's nonempty continuous-path
condition; necessary start and trace-separation criteria are developed here.
The finite-union and approximation classes `M₃` and `M` are in the next files,
where their energy functional is introduced.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- A finite right-continuous step boundary on `[0,1]`, with values in the
extended real line. At a knot the new level is used, giving the
right-continuous convention. A knot at either endpoint is handled by the
one-sided trace API below. -/
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

end StepBoundary

/-- The path set determined by an upper and a lower finite-step boundary.
Paths start at zero and satisfy the strict strip constraints on the entire
closed time interval, matching class `M₁` in the source. -/
def corridorSet (upper lower : StepBoundary) : Set (CadlagPath unitInterval ℝ) :=
  {f | f ⊥ = 0 ∧ ∀ t : unitInterval,
    lower.eval t < (f t : EReal) ∧ (f t : EReal) < upper.eval t}

/-- A finite-step corridor has a continuous admissible path when its set
contains a continuous path starting at zero. -/
def HasContinuousAdmissiblePath (upper lower : StepBoundary) : Prop :=
  ∃ f : C(unitInterval, ℝ), f ⊥ = 0 ∧
    (Skorokhod.ofContinuousMap f : CadlagPath unitInterval ℝ) ∈
      corridorSet upper lower

/-- An `M₁` corridor is specified by its upper and lower finite-step
boundaries. -/
structure M1Corridor where
  upper : StepBoundary
  lower : StepBoundary

/-- The path set represented by an `M₁` corridor. -/
def M1Corridor.toSet (c : M1Corridor) : Set (CadlagPath unitInterval ℝ) :=
  corridorSet c.upper c.lower

/-- A path set belongs to the source's class `M₁` when it is a strict corridor
on `[0,1]` with finite step boundaries, allowing either boundary to take
infinite values. -/
def IsM₁ (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  ∃ c : M1Corridor, G = c.toSet

/-- The origin lies strictly between the two boundary values at time zero.
This condition is needed because every path in an `M₁` corridor starts at
zero. -/
def StartAdmissible (upper lower : StepBoundary) : Prop :=
  lower.eval ⊥ < (0 : EReal) ∧ (0 : EReal) < upper.eval ⊥

/-- At every time the left and right traces of the lower boundary lie strictly
below both traces of the upper boundary. This is the order-theoretic form of
the source's two-sided trace separation condition. -/
def TraceSeparated (upper lower : StepBoundary) : Prop :=
  ∀ t : unitInterval,
    max (lower.leftTrace t) (lower.rightTrace t) <
      min (upper.leftTrace t) (upper.rightTrace t)

/-! ## Corridors in `M₂` -/

/-- A corridor together with the source's admissibility condition that its
intersection with continuous paths is nonempty. -/
structure M2Corridor extends M1Corridor where
  hasContinuousAdmissiblePath : HasContinuousAdmissiblePath upper lower

/-- The path set represented by an `M₂` corridor. -/
def M2Corridor.toSet (c : M2Corridor) : Set (CadlagPath unitInterval ℝ) :=
  c.toM1Corridor.toSet

/-- Class `M₂` consists of the `M₁` corridors whose intersection with the
continuous paths is nonempty. -/
def IsM₂ (G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  ∃ c : M2Corridor, G = c.toSet

theorem isM₁_corridorSet (upper lower : StepBoundary) :
    IsM₁ (corridorSet upper lower) :=
  ⟨⟨upper, lower⟩, rfl⟩

theorem isM₂_corridorSet {upper lower : StepBoundary}
    (h : HasContinuousAdmissiblePath upper lower) :
    IsM₂ (corridorSet upper lower) :=
  ⟨⟨⟨upper, lower⟩, h⟩, rfl⟩

theorem hasContinuousAdmissiblePath_implies_startAdmissible
    {upper lower : StepBoundary}
    (h : HasContinuousAdmissiblePath upper lower) :
    StartAdmissible upper lower := by
  rcases h with ⟨f, hf0, hf⟩
  rcases hf with ⟨_, hcorridor⟩
  have hbounds := hcorridor ⊥
  simpa [StartAdmissible, hf0] using hbounds

theorem hasContinuousAdmissiblePath_implies_traceSeparated
    {upper lower : StepBoundary}
    (h : HasContinuousAdmissiblePath upper lower) :
    TraceSeparated upper lower := by
  classical
  have hstart := hasContinuousAdmissiblePath_implies_startAdmissible h
  rcases h with ⟨f, hf0, hmem⟩
  rcases hmem with ⟨_, hcorridor⟩
  intro t
  by_cases htbot : t = ⊥
  · subst t
    simp only [StepBoundary.leftTrace_bot, StepBoundary.rightTrace_eq_eval,
      max_self, min_self]
    exact hstart.1.trans hstart.2
  · have htpos : (⊥ : unitInterval) < t := bot_lt_iff_ne_bot.mpr htbot
    let knots := lower.knots ∪ upper.knots
    obtain ⟨p, hpt, hp⟩ := StepBoundary.exists_left_gap_finset knots htpos
    have hplower : ∀ q ∈ lower.knots, q < t → q ≤ p := by
      intro q hq hqt
      exact hp q (Finset.mem_union.mpr (Or.inl hq)) hqt
    have hpupper : ∀ q ∈ upper.knots, q < t → q ≤ p := by
      intro q hq hqt
      exact hp q (Finset.mem_union.mpr (Or.inr hq)) hqt
    have hcont : Tendsto (fun s : unitInterval => (f s : EReal)) (𝓝[<] t)
        (𝓝 (f t : EReal)) := by
      exact Filter.Tendsto.mono_left
        ((continuous_coe_real_ereal.comp f.continuous).continuousAt.tendsto)
        nhdsWithin_le_nhds
    have hleftNhds : ∀ᶠ s : unitInterval in 𝓝[<] t, p < s ∧ s < t := by
      have hpOpen : Ioi p ∈ 𝓝 t := Ioi_mem_nhds hpt
      filter_upwards [mem_nhdsWithin_of_mem_nhds hpOpen, self_mem_nhdsWithin] with s hs₁ hs₂
      exact ⟨hs₁, hs₂⟩
    have hlowerEvent : ∀ᶠ s : unitInterval in 𝓝[<] t,
        lower.leftTrace t ≤ (f s : EReal) := by
      filter_upwards [hleftNhds] with s hs
      rw [← StepBoundary.eval_eq_leftTrace_of_between lower hs.1 hs.2 hplower]
      exact le_of_lt (hcorridor s).1
    have hupperEvent : ∀ᶠ s : unitInterval in 𝓝[<] t,
        (f s : EReal) ≤ upper.leftTrace t := by
      filter_upwards [hleftNhds] with s hs
      rw [← StepBoundary.eval_eq_leftTrace_of_between upper hs.1 hs.2 hpupper]
      exact le_of_lt (hcorridor s).2
    have hleftLe : lower.leftTrace t ≤ (f t : EReal) :=
      @le_of_tendsto_of_tendsto EReal unitInterval _ _ _
        (fun _ => lower.leftTrace t) (fun s => (f s : EReal)) (𝓝[<] t)
        (lower.leftTrace t) (f t : EReal)
        (nhdsLT_neBot_of_exists_lt ⟨⊥, htpos⟩)
        tendsto_const_nhds hcont hlowerEvent
    have hrightGe : (f t : EReal) ≤ upper.leftTrace t :=
      @le_of_tendsto_of_tendsto EReal unitInterval _ _ _
        (fun s => (f s : EReal)) (fun _ => upper.leftTrace t) (𝓝[<] t)
        (f t : EReal) (upper.leftTrace t)
        (nhdsLT_neBot_of_exists_lt ⟨⊥, htpos⟩)
        hcont tendsto_const_nhds hupperEvent
    have hleftStrict : lower.leftTrace t < upper.leftTrace t := by
      obtain ⟨s, hps, hst⟩ := exists_between hpt
      rw [← StepBoundary.eval_eq_leftTrace_of_between lower hps hst hplower,
        ← StepBoundary.eval_eq_leftTrace_of_between upper hps hst hpupper]
      exact (hcorridor s).1.trans (hcorridor s).2
    have hleftRight : lower.leftTrace t < upper.rightTrace t := by
      have h := (hcorridor t).2
      simpa [StepBoundary.rightTrace] using hleftLe.trans_lt h
    have hrightLeft : lower.rightTrace t < upper.leftTrace t := by
      have h := (hcorridor t).1
      have h' : lower.rightTrace t < (f t : EReal) := by
        simpa [StepBoundary.rightTrace] using h
      exact h'.trans_le hrightGe
    have hrightRight : lower.rightTrace t < upper.rightTrace t := by
      have h₁ := (hcorridor t).1
      have h₂ := (hcorridor t).2
      simpa [StepBoundary.rightTrace] using h₁.trans h₂
    apply max_lt_iff.mpr
    constructor
    · exact lt_min_iff.mpr ⟨hleftStrict, hleftRight⟩
    · exact lt_min_iff.mpr ⟨hrightLeft, hrightRight⟩

/-- Any continuous admissible path satisfies both the origin condition and
the two-sided trace separation condition. -/
theorem hasContinuousAdmissiblePath_implies_startAndTraceSeparated
    {upper lower : StepBoundary}
    (h : HasContinuousAdmissiblePath upper lower) :
    StartAdmissible upper lower ∧ TraceSeparated upper lower :=
  ⟨hasContinuousAdmissiblePath_implies_startAdmissible h,
    hasContinuousAdmissiblePath_implies_traceSeparated h⟩

end ProbabilityTheory.RandomWalk.Mogulskii
