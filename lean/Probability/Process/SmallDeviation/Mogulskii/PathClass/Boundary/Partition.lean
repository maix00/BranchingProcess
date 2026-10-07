/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Boundary

/-!
# The common time partition of two step boundaries

For a corridor with two finite step boundaries, its deterministic partition
is the union of their jump times together with the time endpoints. The
successor of a partition point is the least later point in this finite set.
This gives the exact open time cells on which both boundary values are
constant, including when either boundary has a jump at time one.
-/

@[expose] public section

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

namespace StepBoundary

/-- The common finite partition points of two step boundaries, including the
endpoints of the time interval. -/
noncomputable def commonKnots (upper lower : StepBoundary) : Finset unitInterval :=
  insert ⊥ (insert ⊤ (upper.knots ∪ lower.knots))

@[simp]
theorem bot_mem_commonKnots (upper lower : StepBoundary) :
    (⊥ : unitInterval) ∈ commonKnots upper lower := by
  simp [commonKnots]

@[simp]
theorem top_mem_commonKnots (upper lower : StepBoundary) :
    (⊤ : unitInterval) ∈ commonKnots upper lower := by
  simp [commonKnots]

theorem mem_commonKnots_of_mem_upper (upper lower : StepBoundary)
    {t : unitInterval} (ht : t ∈ upper.knots) :
    t ∈ commonKnots upper lower := by
  simp [commonKnots, ht]

theorem mem_commonKnots_of_mem_lower (upper lower : StepBoundary)
    {t : unitInterval} (ht : t ∈ lower.knots) :
    t ∈ commonKnots upper lower := by
  simp [commonKnots, ht]

/-- The next common partition point after a nonterminal point. -/
noncomputable def nextCommonKnot (upper lower : StepBoundary)
    (t : unitInterval) (htop : t ≠ ⊤) : unitInterval :=
  (commonKnots upper lower |>.filter fun q => t < q).min'
    (by
      refine ⟨⊤, Finset.mem_filter.mpr ⟨top_mem_commonKnots upper lower,
        lt_top_iff_ne_top.mpr htop⟩⟩)

theorem nextCommonKnot_mem (upper lower : StepBoundary)
    (t : unitInterval) (htop : t ≠ ⊤) :
    nextCommonKnot upper lower t htop ∈ commonKnots upper lower := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

theorem lt_nextCommonKnot (upper lower : StepBoundary)
    (t : unitInterval) (htop : t ≠ ⊤) :
    t < nextCommonKnot upper lower t htop := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

/-- Every common partition point later than `t` lies at or after its
successor. -/
theorem nextCommonKnot_le_of_lt (upper lower : StepBoundary)
    (t q : unitInterval) (htop : t ≠ ⊤)
    (hq : q ∈ commonKnots upper lower) (htq : t < q) :
    nextCommonKnot upper lower t htop ≤ q := by
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hq, htq⟩)

/-- A nonterminal time has a last common partition point strictly before it. -/
theorem exists_prev_commonKnot (upper lower : StepBoundary)
    {s : unitInterval} (hs : ⊥ < s) :
    ∃ p ∈ commonKnots upper lower, p < s ∧
      ∀ q ∈ commonKnots upper lower, q < s → q ≤ p := by
  classical
  let knots := commonKnots upper lower
  let prior := knots.filter fun q => q < s
  let candidates := insert (⊥ : unitInterval) prior
  have hne : candidates.Nonempty := ⟨⊥, Finset.mem_insert_self _ _⟩
  let p := candidates.max' hne
  have hpmem : p ∈ candidates := Finset.max'_mem _ _
  have hps : p < s := by
    rcases Finset.mem_insert.mp hpmem with hp | hp
    · simpa [hp] using hs
    · exact (Finset.mem_filter.mp hp).2
  have hpknots : p ∈ knots := by
    rcases Finset.mem_insert.mp hpmem with hp | hp
    · simp [hp, knots, bot_mem_commonKnots]
    · exact (Finset.mem_filter.mp hp).1
  refine ⟨p, hpknots, hps, ?_⟩
  intro q hq hqs
  have hqprior : q ∈ prior := Finset.mem_filter.mpr ⟨hq, hqs⟩
  exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hqprior)

/-- A time interval belonging to one cell of the common partition. -/
noncomputable def commonCell (upper lower : StepBoundary) (t : unitInterval) :
    Set unitInterval :=
  if htop : t = ⊤ then ∅ else
    Set.Ioo t (nextCommonKnot upper lower t htop)

/-- The union of all cells indexed by nonterminal common partition points. -/
noncomputable def commonCellUnion (upper lower : StepBoundary) :
    Set unitInterval :=
  ⋃ (t : unitInterval)
      (_ : t ∈ ((commonKnots upper lower).erase ⊤ : Set unitInterval)),
    commonCell upper lower t

/-- The open cells are pairwise disjoint. -/
theorem pairwiseDisjoint_commonCells (upper lower : StepBoundary) :
  Set.PairwiseDisjoint (↑((commonKnots upper lower).erase ⊤))
      (commonCell upper lower) := by
  intro p hp q hq hpq
  change Disjoint (commonCell upper lower p) (commonCell upper lower q)
  rw [Set.disjoint_left]
  intro s hps hqs
  have ⟨hpTop, hpMem⟩ := Finset.mem_erase.mp hp
  have ⟨hqTop, hqMem⟩ := Finset.mem_erase.mp hq
  have hpCell : p < s ∧ s < nextCommonKnot upper lower p hpTop := by
    simpa [commonCell, hpTop] using hps
  have hqCell : q < s ∧ s < nextCommonKnot upper lower q hqTop := by
    simpa [commonCell, hqTop] using hqs
  rcases lt_or_gt_of_ne hpq with hpq' | hqp'
  · have hnext : nextCommonKnot upper lower p hpTop ≤ q :=
      nextCommonKnot_le_of_lt upper lower p q hpTop hqMem hpq'
    exact (not_lt_of_ge (le_of_lt (lt_of_lt_of_le hpCell.2 hnext))) hqCell.1
  · have hnext : nextCommonKnot upper lower q hqTop ≤ p :=
      nextCommonKnot_le_of_lt upper lower q p hqTop hpMem hqp'
    exact (not_lt_of_ge (le_of_lt (lt_of_lt_of_le hqCell.2 hnext))) hpCell.1

/-- The union of the common open cells is the interior of the time interval
with all common partition points removed. -/
theorem iUnion_commonCells_eq (upper lower : StepBoundary) :
    commonCellUnion upper lower =
      Set.Ioo ⊥ ⊤ \ (commonKnots upper lower : Set unitInterval) := by
  ext s
  constructor
  · rw [commonCellUnion, Set.mem_iUnion₂]
    rintro ⟨t, ht, hs⟩
    have ⟨htop, htmem⟩ := Finset.mem_erase.mp ht
    have hcell : t < s ∧ s < nextCommonKnot upper lower t htop := by
      simpa [commonCell, htop] using hs
    have hnextmem : nextCommonKnot upper lower t htop ∈
        commonKnots upper lower := nextCommonKnot_mem upper lower t htop
    refine ⟨⟨lt_of_le_of_lt bot_le hcell.1,
      lt_of_lt_of_le hcell.2 le_top⟩, ?_⟩
    intro hsMem
    have hnextle := nextCommonKnot_le_of_lt upper lower t s htop hsMem hcell.1
    exact (not_lt_of_ge hnextle) hcell.2
  · rintro ⟨⟨hsbot, hstop⟩, hsnot⟩
    obtain ⟨t, htmem, hts, htmax⟩ :=
      exists_prev_commonKnot upper lower hsbot
    have htop : t ≠ ⊤ := ne_of_lt (lt_trans hts hstop)
    have hnextgt : t < nextCommonKnot upper lower t htop :=
      lt_nextCommonKnot upper lower t htop
    have hnextmem : nextCommonKnot upper lower t htop ∈
        commonKnots upper lower := nextCommonKnot_mem upper lower t htop
    have hstnext : s < nextCommonKnot upper lower t htop := by
      by_contra hnot
      have hle : nextCommonKnot upper lower t htop ≤ s := le_of_not_gt hnot
      have hne : nextCommonKnot upper lower t htop ≠ s := by
        intro heq
        exact hsnot (heq ▸ hnextmem)
      have hlt : nextCommonKnot upper lower t htop < s := lt_of_le_of_ne hle hne
      exact (not_lt_of_ge (htmax _ hnextmem hlt)) hnextgt
    have htErase : t ∈ (commonKnots upper lower).erase ⊤ :=
      Finset.mem_erase.mpr ⟨htop, htmem⟩
    rw [commonCellUnion, Set.mem_iUnion₂]
    refine ⟨t, htErase, ?_⟩
    simpa [commonCell, htop] using (show s ∈ Set.Ioo t
      (nextCommonKnot upper lower t htop) from ⟨hts, hstnext⟩)

/-- There is no common partition point strictly between a partition point and
its successor. -/
theorem no_commonKnot_between_next (upper lower : StepBoundary)
    (t q : unitInterval) (htop : t ≠ ⊤)
    (hq : q ∈ commonKnots upper lower) (htq : t < q)
    (hqn : q < nextCommonKnot upper lower t htop) : False := by
  exact (not_lt_of_ge (nextCommonKnot_le_of_lt upper lower t q htop hq htq)) hqn

/-- A boundary whose knots lie in the common partition is constant on the
open cell from a partition point to its successor. The value at the left
endpoint is the right-continuous level, so jumps at that endpoint are
assigned to the cell on its right. -/
theorem eval_eq_rightTrace_on_nextCell (b upper lower : StepBoundary)
    (hknots : ∀ q ∈ b.knots, q ∈ commonKnots upper lower)
    (t s : unitInterval)
    (htop : t ≠ ⊤) (hts : t < s)
    (hs : s < nextCommonKnot upper lower t htop) :
    b.eval s = b.rightTrace t := by
  apply b.eval_eq_rightTrace_of_between hts hs
  intro q hq htq
  exact nextCommonKnot_le_of_lt upper lower t q htop
    (hknots q hq) htq

theorem upper_eval_eq_rightTrace_on_nextCell (upper lower : StepBoundary)
    (t s : unitInterval)
    (htop : t ≠ ⊤) (hts : t < s)
    (hs : s < nextCommonKnot upper lower t htop) :
    upper.eval s = upper.rightTrace t :=
  eval_eq_rightTrace_on_nextCell upper upper lower
    (fun _ hq => mem_commonKnots_of_mem_upper upper lower hq)
    t s htop hts hs

theorem lower_eval_eq_rightTrace_on_nextCell (upper lower : StepBoundary)
    (t s : unitInterval)
    (htop : t ≠ ⊤) (hts : t < s)
    (hs : s < nextCommonKnot upper lower t htop) :
    lower.eval s = lower.rightTrace t :=
  eval_eq_rightTrace_on_nextCell lower upper lower
    (fun _ hq => mem_commonKnots_of_mem_lower upper lower hq)
    t s htop hts hs

end StepBoundary

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

end
