/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.Monotone

/-!
# First nonnegative unit-window times on continuous paths

## Public declarations

- `ProbabilityTheory.IsNonnegativeWindowStart f t` means
  $f(t+u)\ge f(t)$ for every $u\in[0,1]$; the fixed-time event is Borel and
  the set of eligible start times is closed.
- `ProbabilityTheory.exists_earliestNonnegativeWindowStart` gives a least
  eligible start whenever one exists.
- `ProbabilityTheory.firstNonnegativeWindowStart` is this least start, with
  value $\infty$ if no eligible start exists.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo f s` is the least
  eligible start with $t+1\le s$, with value $\infty$ when the finite-horizon
  candidate set is empty.
- `ProbabilityTheory.firstNonnegativeWindowStart_eq_coe_iff` and
  `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_coe_iff` characterize
  the finite values by eligibility and minimality.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_mono`,
  `firstNonnegativeWindowStart_le_upTo`,
  `firstNonnegativeWindowStartUpTo_eq_first_of_le`, and
  `firstNonnegativeWindowStartUpTo_eq_first_of_ne_top` give the comparison
  and stabilization relations between finite-horizon and unrestricted times.

These are the path-time definitions from Erwin Bolthausen, *On a Functional
Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Section 2,
definition (2.1), Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

/-- A length-one window of a continuous path lies above its initial value. -/
def IsNonnegativeWindowStart (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) : Prop :=
  ∀ u : Set.Icc (0 : ℝ≥0) 1, f t ≤ f (t + u)

/-- For a fixed continuous path, eligible window starting times form a
closed set. This supplies the attainment of the first eligible time. -/
theorem isClosed_nonnegativeWindowStarts (f : C(ℝ≥0, ℝ)) :
    IsClosed {t : ℝ≥0 | IsNonnegativeWindowStart f t} := by
  have hset : {t : ℝ≥0 | IsNonnegativeWindowStart f t} =
      ⋂ u : Set.Icc (0 : ℝ≥0) 1,
        {t | f t ≤ f (t + u)} := by
    ext t
    simp [IsNonnegativeWindowStart]
  rw [hset]
  apply isClosed_iInter
  intro u
  exact isClosed_le f.continuous
    (f.continuous.comp (continuous_id.add continuous_const))

/-- At a fixed starting time, eligibility of the window is a Borel
path event. This supplies the fixed-time events in Bolthausen's
rational approximation of $T^s$ in the proof of Lemma 2.1. -/
theorem measurableSet_nonnegativeWindowStart (t : ℝ≥0) :
    MeasurableSet {f : C(ℝ≥0, ℝ) |
      IsNonnegativeWindowStart f t} := by
  have hset : {f : C(ℝ≥0, ℝ) | IsNonnegativeWindowStart f t} =
      ⋂ u : Set.Icc (0 : ℝ≥0) 1,
        {f | f t ≤ f (t + u)} := by
    ext f
    simp [IsNonnegativeWindowStart]
  rw [hset]
  have hclosed (u : Set.Icc (0 : ℝ≥0) 1) :
      IsClosed {f : C(ℝ≥0, ℝ) | f t ≤ f (t + u)} :=
    isClosed_le (continuous_eval_const t)
      (continuous_eval_const (t + u))
  exact (isClosed_iInter hclosed).measurableSet

/-- A nonempty closed family of eligible starts has a first member. -/
theorem exists_earliestNonnegativeWindowStart
    (f : C(ℝ≥0, ℝ))
    (h : ∃ t : ℝ≥0, IsNonnegativeWindowStart f t) :
    ∃ t : ℝ≥0, IsNonnegativeWindowStart f t ∧
      ∀ s : ℝ≥0, IsNonnegativeWindowStart f s → t ≤ s := by
  let starts : Set ℝ≥0 := {t | IsNonnegativeWindowStart f t}
  have hnonempty : starts.Nonempty := h
  have hclosed : IsClosed starts := isClosed_nonnegativeWindowStarts f
  have hbelow : BddBelow starts := ⟨0, fun _ _ => bot_le⟩
  exact ⟨sInf starts, hclosed.csInf_mem hnonempty hbelow,
    fun s hs => csInf_le hbelow hs⟩

/-- First length-one window above its starting level; the value is
infinite if the path has no such window. This is $T=T^\infty$ in
Bolthausen, Section 2, equation (2.1). -/
noncomputable def firstNonnegativeWindowStart
    (f : C(ℝ≥0, ℝ)) : WithTop ℝ≥0 :=
  if _h : ∃ t : ℝ≥0, IsNonnegativeWindowStart f t then
    (sInf {t | IsNonnegativeWindowStart f t} : ℝ≥0)
  else ⊤

/-- The finite value of the first-window time is characterized by
eligibility and minimality. -/
theorem firstNonnegativeWindowStart_eq_coe_iff
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0) :
    firstNonnegativeWindowStart f = t ↔
      IsNonnegativeWindowStart f t ∧
        ∀ s : ℝ≥0, IsNonnegativeWindowStart f s → t ≤ s := by
  classical
  unfold firstNonnegativeWindowStart
  split_ifs with h
  · let starts : Set ℝ≥0 := {x | IsNonnegativeWindowStart f x}
    have hnonempty : starts.Nonempty := h
    have hclosed : IsClosed starts := isClosed_nonnegativeWindowStarts f
    have hbelow : BddBelow starts := ⟨0, fun _ _ => bot_le⟩
    constructor
    · intro heq
      have ht : sInf starts = t := WithTop.coe_injective heq
      constructor
      · exact ht ▸ hclosed.csInf_mem hnonempty hbelow
      · intro s hs
        rw [← ht]
        exact csInf_le hbelow hs
    · rintro ⟨ht, hmin⟩
      congr 1
      apply le_antisymm
      · exact csInf_le hbelow ht
      · exact le_csInf hnonempty fun s hs => hmin s hs
  · constructor
    · intro heq
      exact False.elim (WithTop.coe_ne_top heq.symm)
    · rintro ⟨ht, _⟩
      exact False.elim (h ⟨t, ht⟩)

/-- The first eligible window fully contained in the time interval
$[0,s]$. This is $T^s$ in Bolthausen, Section 2, equation (2.1). -/
noncomputable def firstNonnegativeWindowStartUpTo
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) : WithTop ℝ≥0 :=
  if _h : ∃ t : ℝ≥0, t + 1 ≤ s ∧ IsNonnegativeWindowStart f t then
    (sInf {t | t + 1 ≤ s ∧ IsNonnegativeWindowStart f t} : ℝ≥0)
  else ⊤

/-- The finite value of $T^s$ is its least eligible start before $s-1$. -/
theorem firstNonnegativeWindowStartUpTo_eq_coe_iff
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0) :
    firstNonnegativeWindowStartUpTo f s = t ↔
      t + 1 ≤ s ∧ IsNonnegativeWindowStart f t ∧
        ∀ r : ℝ≥0, r + 1 ≤ s →
          IsNonnegativeWindowStart f r → t ≤ r := by
  classical
  unfold firstNonnegativeWindowStartUpTo
  split_ifs with h
  · let starts : Set ℝ≥0 :=
      {x | x + 1 ≤ s ∧ IsNonnegativeWindowStart f x}
    have hnonempty : starts.Nonempty := h
    have hclosed : IsClosed starts := by
      exact (isClosed_le (continuous_id.add continuous_const)
        continuous_const).inter
          (isClosed_nonnegativeWindowStarts f)
    have hbelow : BddBelow starts := ⟨0, fun _ _ => bot_le⟩
    constructor
    · intro heq
      have ht : sInf starts = t := WithTop.coe_injective heq
      have hmem : t ∈ starts := ht ▸ hclosed.csInf_mem hnonempty hbelow
      exact ⟨hmem.1, hmem.2, fun r _ hr => by
        rw [← ht]
        exact csInf_le hbelow ⟨‹r + 1 ≤ s›, hr⟩⟩
    · rintro ⟨hts, ht, hmin⟩
      congr 1
      apply le_antisymm
      · exact csInf_le hbelow ⟨hts, ht⟩
      · exact le_csInf hnonempty fun r hr => hmin r hr.1 hr.2
  · constructor
    · intro heq
      exact False.elim (WithTop.coe_ne_top heq.symm)
    · rintro ⟨hts, ht, _⟩
      exact False.elim (h ⟨t, hts, ht⟩)

/-- Increasing the horizon can only advance the first eligible window. -/
theorem firstNonnegativeWindowStartUpTo_mono
    (f : C(ℝ≥0, ℝ)) {s s' : ℝ≥0} (hss' : s ≤ s') :
    firstNonnegativeWindowStartUpTo f s' ≤
      firstNonnegativeWindowStartUpTo f s := by
  classical
  by_cases hfinite : ∃ t : ℝ≥0, t + 1 ≤ s ∧ IsNonnegativeWindowStart f t
  · have hfinite' : ∃ t : ℝ≥0, t + 1 ≤ s' ∧ IsNonnegativeWindowStart f t := by
      obtain ⟨t, hts, ht⟩ := hfinite
      exact ⟨t, hts.trans hss', ht⟩
    simp only [firstNonnegativeWindowStartUpTo, dite_eq_left hfinite,
      dite_eq_left hfinite', WithTop.coe_le_coe]
    apply le_csInf hfinite
    intro t ht
    exact csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨ht.1.trans hss', ht.2⟩
  · simp [firstNonnegativeWindowStartUpTo, hfinite]

/-- The unrestricted first window occurs no later than one found before a
finite horizon. -/
theorem firstNonnegativeWindowStart_le_upTo
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    firstNonnegativeWindowStart f ≤
      firstNonnegativeWindowStartUpTo f s := by
  classical
  by_cases hfinite : ∃ t : ℝ≥0, t + 1 ≤ s ∧ IsNonnegativeWindowStart f t
  · have hnonempty : ∃ t : ℝ≥0, IsNonnegativeWindowStart f t := by
      obtain ⟨t, _, ht⟩ := hfinite
      exact ⟨t, ht⟩
    simp only [firstNonnegativeWindowStart, firstNonnegativeWindowStartUpTo,
      dite_eq_left hnonempty, dite_eq_left hfinite, WithTop.coe_le_coe]
    apply le_csInf hfinite
    intro t ht
    exact csInf_le ⟨0, fun _ _ => bot_le⟩ ht.2
  · simp [firstNonnegativeWindowStartUpTo, hfinite]

/-- Once the finite horizon contains the unrestricted first eligible
window, the two first-window times agree. -/
theorem firstNonnegativeWindowStartUpTo_eq_first_of_le
    (f : C(ℝ≥0, ℝ)) {s t : ℝ≥0}
    (ht : firstNonnegativeWindowStart f = t) (hts : t + 1 ≤ s) :
    firstNonnegativeWindowStartUpTo f s = t := by
  obtain ⟨heligible, hfirst⟩ :=
    (firstNonnegativeWindowStart_eq_coe_iff f t).mp ht
  exact (firstNonnegativeWindowStartUpTo_eq_coe_iff f s t).mpr
    ⟨hts, heligible, fun r _ hr => hfirst r hr⟩

/-- Whenever a finite-horizon eligible window exists, it is also the
unrestricted first eligible window. -/
theorem firstNonnegativeWindowStartUpTo_eq_first_of_ne_top
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (hfinite : firstNonnegativeWindowStartUpTo f s ≠ ⊤) :
    firstNonnegativeWindowStartUpTo f s = firstNonnegativeWindowStart f := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have htime : firstNonnegativeWindowStartUpTo f s = t := ht.symm
  have hbound := (firstNonnegativeWindowStartUpTo_eq_coe_iff f s t).mp htime |>.1
  have hfirstle := firstNonnegativeWindowStart_le_upTo f s
  have hfirstfinite : firstNonnegativeWindowStart f ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hfirstle (htime ▸ WithTop.coe_lt_top t))
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfirstfinite
  have hrle : r ≤ t := WithTop.coe_le_coe.mp (by
    calc
      (r : WithTop ℝ≥0) = firstNonnegativeWindowStart f := hr
      _ ≤ firstNonnegativeWindowStartUpTo f s := hfirstle
      _ = (t : WithTop ℝ≥0) := htime)
  have hrs : r + 1 ≤ s :=
    (add_le_add_left hrle 1).trans hbound
  exact (firstNonnegativeWindowStartUpTo_eq_first_of_le
    f hr.symm hrs).trans hr


end ProbabilityTheory
