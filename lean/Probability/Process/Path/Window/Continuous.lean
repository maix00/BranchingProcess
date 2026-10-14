/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Continuous
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Data.NNRat.Encodable

/-!
# Windows above their starting level on a continuous path

The public definition and theorems in this file are:

- `ProbabilityTheory.IsNonnegativeWindowStart`: for a continuous path $f$,
  $f(t+u)\ge f(t)$ for every $u\in[0,1]$.
- `ProbabilityTheory.isClosed_nonnegativeWindowStarts`: the set of such
  starting times is closed.
- `ProbabilityTheory.measurableSet_nonnegativeWindowStart`:
  for fixed $t$, the path event that the window at $t$ stays above
  its starting value is Borel measurable.
- `ProbabilityTheory.ApproxNonnegativeWindowStart`:
  $f(r)\le f(r+i/(n+1))+1/(n+1)$ for $1\le i\le n$.
- `ProbabilityTheory.measurableSet_approxNonnegativeWindowStart`:
  this finite-grid path event is Borel measurable.
- `ProbabilityTheory.HasApproxWindowBefore`:
  a rational start $r\le u+1/(n+1)$ satisfies the finite-grid
  inequalities in Bolthausen's approximation.
- `ProbabilityTheory.measurableSet_hasApproxWindowBefore`:
  the corresponding countable union of finite-grid events is Borel.
- `ProbabilityTheory.HasApproxFirstWindowBefore`:
  the countable intersection over all grid sizes of the rational-start
  events appearing in Bolthausen's proof of Lemma 2.1.
- `ProbabilityTheory.measurableSet_hasApproxFirstWindowBefore`:
  this countable-intersection path event is Borel.
- `ProbabilityTheory.exists_earliestNonnegativeWindowStart`: if this set
  is nonempty, it has a least element.
- `ProbabilityTheory.firstNonnegativeWindowStart`: the earliest eligible
  time, with value $\infty$ when there is no eligible time.
- `ProbabilityTheory.firstNonnegativeWindowStart_eq_coe_iff`:
  $T(f)=t<\infty$ precisely when $t$ is an eligible start and no
  earlier start is eligible.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo`:
  $T^s(f)=\inf\{t:t+1\le s,\ f(t+u)\ge f(t)\ (0\le u\le1)\}$,
  with value $\infty$ if the set is empty.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_coe_iff`:
  $T^s(f)=t<\infty$ precisely when $t+1\le s$, the window at $t$
  is eligible, and $t$ precedes every other eligible start in $[0,s]$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_mono`:
  $s\le s'$ implies $T^{s'}(f)\le T^s(f)$.
- `ProbabilityTheory.firstNonnegativeWindowStart_le_upTo`:
  $T(f)\le T^s(f)$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_first_of_le`:
  $T(f)=t$ and $t+1\le s$ imply $T^s(f)=t$.

These are deterministic ingredients of the first-window time $T^s$ in
Erwin Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Section 2, definition (2.1),
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open scoped NNReal

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

/-- The finite-grid inequality in Bolthausen's rational approximation
to $\{T^s\le u\}$, Lemma 2.1, p. 481. -/
def ApproxNonnegativeWindowStart
    (n : ℕ) (r : ℝ≥0) (f : C(ℝ≥0, ℝ)) : Prop :=
  ∀ i : Fin n,
    f r ≤ f (r + ((i : ℝ≥0) + 1) / (n + 1)) +
      (1 : ℝ) / (n + 1)

/-- Each fixed rational-start finite-grid inequality from the proof of
Bolthausen's Lemma 2.1 is a Borel path event. -/
theorem measurableSet_approxNonnegativeWindowStart
    (n : ℕ) (r : ℝ≥0) :
    MeasurableSet {f : C(ℝ≥0, ℝ) |
      ApproxNonnegativeWindowStart n r f} := by
  have hset : {f : C(ℝ≥0, ℝ) |
      ApproxNonnegativeWindowStart n r f} =
      ⋂ i : Fin n,
        {f | f r ≤ f (r + ((i : ℝ≥0) + 1) / (n + 1)) +
          (1 : ℝ) / (n + 1)} := by
    ext f
    simp [ApproxNonnegativeWindowStart]
  rw [hset]
  have hclosed (i : Fin n) :
      IsClosed {f : C(ℝ≥0, ℝ) |
        f r ≤ f (r + ((i : ℝ≥0) + 1) / (n + 1)) +
          (1 : ℝ) / (n + 1)} :=
    isClosed_le (continuous_eval_const r)
      ((continuous_eval_const _).add continuous_const)
  exact (isClosed_iInter hclosed).measurableSet

/-- The rational-start event in Bolthausen's approximation of
$\{T^s\le u\}$ in the proof of Lemma 2.1. -/
def HasApproxWindowBefore
    (n : ℕ) (u : ℝ≥0) (f : C(ℝ≥0, ℝ)) : Prop :=
  ∃ r : ℚ≥0, (r : ℝ≥0) ≤ u + 1 / (n + 1) ∧
    ApproxNonnegativeWindowStart n (r : ℝ≥0) f

/-- The rational-start finite-grid event is a countable union of Borel
path events. -/
theorem measurableSet_hasApproxWindowBefore (n : ℕ) (u : ℝ≥0) :
    MeasurableSet {f : C(ℝ≥0, ℝ) | HasApproxWindowBefore n u f} := by
  have hset : {f : C(ℝ≥0, ℝ) | HasApproxWindowBefore n u f} =
      ⋃ r : ℚ≥0, {f | (r : ℝ≥0) ≤ u + 1 / (n + 1) ∧
        ApproxNonnegativeWindowStart n (r : ℝ≥0) f} := by
    ext f
    simp [HasApproxWindowBefore]
  rw [hset]
  apply MeasurableSet.iUnion
  intro r
  by_cases hr : (r : ℝ≥0) ≤ u + 1 / (n + 1)
  · have hr' : (r : ℝ≥0) ≤ u + ((n : ℝ≥0) + 1)⁻¹ := by
      simpa only [one_div] using hr
    have heq : {f : C(ℝ≥0, ℝ) |
        (r : ℝ≥0) ≤ u + 1 / (n + 1) ∧
          ApproxNonnegativeWindowStart n (r : ℝ≥0) f} =
        {f | ApproxNonnegativeWindowStart n (r : ℝ≥0) f} := by
      ext f
      simp [hr']
    rw [heq]
    exact measurableSet_approxNonnegativeWindowStart n (r : ℝ≥0)
  · have hr' : ¬ (r : ℝ≥0) ≤ u + ((n : ℝ≥0) + 1)⁻¹ := by
      simpa only [one_div] using hr
    have heq : {f : C(ℝ≥0, ℝ) |
        (r : ℝ≥0) ≤ u + 1 / (n + 1) ∧
          ApproxNonnegativeWindowStart n (r : ℝ≥0) f} = ∅ := by
      ext f
      simp [hr']
    rw [heq]
    exact MeasurableSet.empty

/-- The countable rational approximation appearing on the right side
of Bolthausen's formula for $\{T^s\le u\}$ in Lemma 2.1. -/
def HasApproxFirstWindowBefore
    (u : ℝ≥0) (f : C(ℝ≥0, ℝ)) : Prop :=
  ∀ n : ℕ, HasApproxWindowBefore n u f

/-- The countable rational approximation is a Borel path event. -/
theorem measurableSet_hasApproxFirstWindowBefore (u : ℝ≥0) :
    MeasurableSet {f : C(ℝ≥0, ℝ) |
      HasApproxFirstWindowBefore u f} := by
  have hset : {f : C(ℝ≥0, ℝ) | HasApproxFirstWindowBefore u f} =
      ⋂ n : ℕ, {f | HasApproxWindowBefore n u f} := by
    ext f
    simp [HasApproxFirstWindowBefore]
  rw [hset]
  exact MeasurableSet.iInter fun n =>
    measurableSet_hasApproxWindowBefore n u

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

end ProbabilityTheory

end
