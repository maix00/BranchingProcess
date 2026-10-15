/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.Continuous
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Continuity of the first nonnegative unit-window time

The public theorems in this file are:

- `ProbabilityTheory.isClosed_nonnegativeWindowStart_pairs`:
  the set of pairs $(f,t)$ satisfying $f(t+u)\ge f(t)$ for
  every $0\le u\le1$ is closed.
- `ProbabilityTheory.isClosed_hasNonnegativeWindowStartAtMost`:
  for fixed $a$, the set of paths with an eligible start in $[0,a]$
  is closed. Thus the first-window time is lower semicontinuous.
- `ProbabilityTheory.lowerSemicontinuous_firstNonnegativeWindowStart`:
  $f\mapsto T(f)$ is lower semicontinuous.
- `ProbabilityTheory.exists_nonnegativeWindowStart_before_of_strict_tail`:
  a strict unit-length tail above $f(t)$ yields an eligible start
  before the tail begins, by minimizing on the preceding interval.
- `ProbabilityTheory.isOpen_strictUnitTail`:
  the condition $f(t)<f(u)$ for all $u\in[b,b+1]$ is open in $f$.
- `ProbabilityTheory.upperSemicontinuousAt_firstNonnegativeWindowStart_of_strictTails`:
  strict unit tails beginning arbitrarily soon after $T(f)$ imply
  upper semicontinuity of $T$ at $f$.
- `ProbabilityTheory.strictUnitTails_of_strictInteriorAndEndpoint`:
  strict positivity throughout $(t,t+1]$ produces these tails.
- `ProbabilityTheory.continuousAt_firstNonnegativeWindowStart_of_strictWindow`:
  $T$ is continuous at a path whose first unit window is strictly
  above its start at every later point.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_first_of_lt_cutoff`:
  $T(f)<s-1$ implies $T^s(f)=T(f)$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_top_of_cutoff_lt`:
  $s-1<T(f)$ implies $T^s(f)=\infty$.
- `ProbabilityTheory.continuousAt_firstNonnegativeWindowStartUpTo_of_ne_cutoff`:
  continuity of $T$ at $f$ and $T(f)\ne s-1$ imply continuity
  of $T^s$ at $f$.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_top_of_lt_one`:
  $s<1$ leaves no time for a full unit window.

These are the deterministic lower-semicontinuity ingredients of
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Lemma 2.4, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter
open scoped NNReal Topology

/-- Eligibility of a unit window is closed jointly in its path and
starting time. -/
theorem isClosed_nonnegativeWindowStart_pairs :
    IsClosed {p : C(ℝ≥0, ℝ) × ℝ≥0 |
      IsNonnegativeWindowStart p.1 p.2} := by
  have hset : {p : C(ℝ≥0, ℝ) × ℝ≥0 |
      IsNonnegativeWindowStart p.1 p.2} =
      ⋂ u : Set.Icc (0 : ℝ≥0) 1,
        {p | p.1 p.2 ≤ p.1 (p.2 + u)} := by
    ext p
    simp [IsNonnegativeWindowStart]
  rw [hset]
  apply isClosed_iInter
  intro u
  have hleft : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2) :=
    continuous_eval.comp (continuous_fst.prodMk continuous_snd)
  have hright : Continuous (fun p : C(ℝ≥0, ℝ) × ℝ≥0 =>
      p.1 (p.2 + u)) :=
    continuous_eval.comp
      (continuous_fst.prodMk (continuous_snd.add continuous_const))
  exact isClosed_le hleft hright

/-- If eligible starts are restricted to $[0,a]$, their existence is
a closed condition on the path. This is Bolthausen's lower
semicontinuity argument in Lemma 2.4. -/
theorem isClosed_hasNonnegativeWindowStartAtMost (a : ℝ≥0) :
    IsClosed {f : C(ℝ≥0, ℝ) |
      ∃ t : ℝ≥0, t ≤ a ∧ IsNonnegativeWindowStart f t} := by
  let K : Set ℝ≥0 := Set.Icc 0 a
  have hK : IsCompact K := isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (C(ℝ≥0, ℝ) × K) :=
    {p | IsNonnegativeWindowStart p.1 p.2.1}
  have hS : IsClosed S := by
    have hcont : Continuous (fun p : C(ℝ≥0, ℝ) × K =>
        ((p.1, p.2.1) : C(ℝ≥0, ℝ) × ℝ≥0)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact isClosed_nonnegativeWindowStart_pairs.preimage hcont
  have hproj : IsClosed ((Prod.fst : C(ℝ≥0, ℝ) × K → C(ℝ≥0, ℝ)) '' S) :=
    isClosedMap_fst_of_compactSpace S hS
  convert hproj using 1
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_image, S]
  constructor
  · rintro ⟨t, hta, ht⟩
    exact ⟨(f, ⟨t, ⟨bot_le, hta⟩⟩), ht, rfl⟩
  · rintro ⟨p, hp, hpf⟩
    cases p with
    | mk g t =>
      change g = f at hpf
      subst g
      exact ⟨t.1, t.2.2, hp⟩

/-- The first eligible start lies before $a$ precisely when some
eligible start lies before $a$. -/
theorem firstNonnegativeWindowStart_le_coe_iff
    (f : C(ℝ≥0, ℝ)) (a : ℝ≥0) :
    firstNonnegativeWindowStart f ≤ (a : WithTop ℝ≥0) ↔
      ∃ t : ℝ≥0, t ≤ a ∧ IsNonnegativeWindowStart f t := by
  constructor
  · intro h
    have hfinite : firstNonnegativeWindowStart f < ⊤ :=
      lt_of_le_of_lt h (WithTop.coe_lt_top a)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfinite.ne
    have hchar := (firstNonnegativeWindowStart_eq_coe_iff f t).mp ht.symm
    exact ⟨t, WithTop.coe_le_coe.mp (ht.symm ▸ h), hchar.1⟩
  · rintro ⟨t, hta, ht⟩
    obtain ⟨r, hr, hleast⟩ :=
      exists_earliestNonnegativeWindowStart f ⟨t, ht⟩
    have hfirst := (firstNonnegativeWindowStart_eq_coe_iff f r).mpr
      ⟨hr, hleast⟩
    rw [hfirst]
    exact WithTop.coe_le_coe.mpr ((hleast t ht).trans hta)

/-- The first eligible unit-window time is lower semicontinuous on
the space of continuous paths. This is the second part of the proof
of Bolthausen's Lemma 2.4. -/
theorem lowerSemicontinuous_firstNonnegativeWindowStart :
    LowerSemicontinuous
      (firstNonnegativeWindowStart : C(ℝ≥0, ℝ) → WithTop ℝ≥0) := by
  change Semicontinuous (firstNonnegativeWindowStart · > ·)
  rw [semicontinuous_iff_isOpen]
  intro a
  cases a with
  | top =>
      simpa using (isOpen_empty : IsOpen (∅ : Set C(ℝ≥0, ℝ)))
  | coe a =>
      have hclosed : IsClosed {f : C(ℝ≥0, ℝ) |
          firstNonnegativeWindowStart f ≤ (a : WithTop ℝ≥0)} := by
        convert isClosed_hasNonnegativeWindowStartAtMost a using 1
        ext f
        exact firstNonnegativeWindowStart_le_coe_iff f a
      convert hclosed.isOpen_compl using 1
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]

/-- Bolthausen's minimizer construction in the upper-semicontinuity
part of Lemma 2.4. A path strictly above its value at $t$ on the
unit-length tail $[b,b+1]$ has an eligible start in $[t,b)$. -/
theorem exists_nonnegativeWindowStart_before_of_strict_tail
    (f : C(ℝ≥0, ℝ)) {t b : ℝ≥0} (htb : t < b)
    (htail : ∀ u : ℝ≥0, b ≤ u → u ≤ b + 1 → f t < f u) :
    ∃ r : ℝ≥0, t ≤ r ∧ r < b ∧ IsNonnegativeWindowStart f r := by
  have hne : (Set.Icc t b).Nonempty := ⟨t, le_rfl, htb.le⟩
  obtain ⟨r, hr, hmin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc t b)).exists_isMinOn
      hne f.continuous.continuousOn
  have hrb : r < b := by
    refine hr.2.lt_of_ne ?_
    intro heq
    have hrt : f r ≤ f t := hmin ⟨le_rfl, htb.le⟩
    rw [heq] at hrt
    exact (not_le_of_gt (htail b le_rfl (le_add_of_nonneg_right (by positivity)))) hrt
  refine ⟨r, hr.1, hrb, ?_⟩
  intro v
  have hrv : r + v ≤ b + 1 := by
    calc
      r + v ≤ r + 1 := add_le_add_right v.property.2 r
      _ ≤ b + 1 := add_le_add_left hr.2 1
  by_cases hbefore : r + v ≤ b
  · exact hmin ⟨hr.1.trans (le_add_of_nonneg_right v.property.1), hbefore⟩
  · have hb : b ≤ r + v := le_of_not_ge hbefore
    exact (hmin ⟨le_rfl, htb.le⟩).trans
      (htail (r + v) hb hrv).le

/-- Strict separation from the starting value on a compact unit tail
persists under perturbation of the path. -/
theorem isOpen_strictUnitTail (t b : ℝ≥0) :
    IsOpen {f : C(ℝ≥0, ℝ) |
      ∀ u : ℝ≥0, b ≤ u → u ≤ b + 1 → f t < f u} := by
  let K : Set ℝ≥0 := Set.Icc b (b + 1)
  let : CompactSpace K :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact K)
  let S : Set (C(ℝ≥0, ℝ) × K) := {p | p.1 p.2.1 ≤ p.1 t}
  have hS : IsClosed S := by
    have hleft : Continuous (fun p : C(ℝ≥0, ℝ) × K => p.1 p.2.1) :=
      continuous_eval.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have hright : Continuous (fun p : C(ℝ≥0, ℝ) × K => p.1 t) :=
      (continuous_eval_const t).comp continuous_fst
    exact isClosed_le hleft hright
  have hproj : IsClosed ((Prod.fst : C(ℝ≥0, ℝ) × K → C(ℝ≥0, ℝ)) '' S) :=
    isClosedMap_fst_of_compactSpace S hS
  convert hproj.isOpen_compl using 1
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, S]
  constructor
  · intro hf ⟨p, hp, hpf⟩
    cases p with
    | mk g u =>
      change g = f at hpf
      subst g
      exact (not_le_of_gt (hf u.1 u.2.1 u.2.2)) hp
  · intro hf u hbu hub
    by_contra hle
    apply hf
    exact ⟨(f, ⟨u, hbu, hub⟩), le_of_not_gt hle, rfl⟩

/-- The strict-tail condition in Bolthausen's Lemma 2.4 implies
upper semicontinuity of the first-window time. -/
theorem upperSemicontinuousAt_firstNonnegativeWindowStart_of_strictTails
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStart f = t)
    (htails : ∀ a : ℝ≥0, t < a →
      ∃ b : ℝ≥0, t < b ∧ b < a ∧
        ∀ u : ℝ≥0, b ≤ u → u ≤ b + 1 → f t < f u) :
    UpperSemicontinuousAt firstNonnegativeWindowStart f := by
  rw [upperSemicontinuousAt_iff]
  intro a ha
  cases a with
  | top =>
      obtain ⟨b, htb, _, htail⟩ := htails (t + 1)
        (lt_add_of_pos_right t (by norm_num))
      have hnb : ∀ᶠ g in 𝓝 f,
          ∀ u : ℝ≥0, b ≤ u → u ≤ b + 1 → g t < g u :=
        (isOpen_strictUnitTail t b).mem_nhds htail
      filter_upwards [hnb] with g hg
      obtain ⟨r, _, _, hr⟩ :=
        exists_nonnegativeWindowStart_before_of_strict_tail g htb hg
      have hle : firstNonnegativeWindowStart g ≤ (r : WithTop ℝ≥0) :=
        (firstNonnegativeWindowStart_le_coe_iff g r).mpr ⟨r, le_rfl, hr⟩
      exact lt_of_le_of_lt hle (WithTop.coe_lt_top r)
  | coe a =>
      have hta : t < a := WithTop.coe_lt_coe.mp (hfirst ▸ ha)
      obtain ⟨b, htb, hba, htail⟩ := htails a hta
      have hnb : ∀ᶠ g in 𝓝 f,
          ∀ u : ℝ≥0, b ≤ u → u ≤ b + 1 → g t < g u :=
        (isOpen_strictUnitTail t b).mem_nhds htail
      filter_upwards [hnb] with g hg
      obtain ⟨r, _, hrb, hr⟩ :=
        exists_nonnegativeWindowStart_before_of_strict_tail g htb hg
      have hle : firstNonnegativeWindowStart g ≤ (r : WithTop ℝ≥0) :=
        (firstNonnegativeWindowStart_le_coe_iff g r).mpr ⟨r, le_rfl, hr⟩
      exact lt_of_le_of_lt hle (WithTop.coe_lt_coe.mpr (hrb.trans hba))

/-- Strict positivity in the interior of the first unit window and
at its endpoint supplies the short strict tails used in Bolthausen's
upper-semicontinuity proof. -/
theorem strictUnitTails_of_strictInteriorAndEndpoint
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0)
    (hinterior : ∀ u : ℝ≥0, 0 < u → u < 1 → f t < f (t + u))
    (hendpoint : f t < f (t + 1)) :
    ∀ a : ℝ≥0, t < a →
      ∃ b : ℝ≥0, t < b ∧ b < a ∧
        ∀ u : ℝ≥0, b ≤ u → u ≤ b + 1 → f t < f u := by
  let U : Set ℝ≥0 := {u | f t < f u}
  have hUopen : IsOpen U := isOpen_lt continuous_const f.continuous
  have hU : t + 1 ∈ U := hendpoint
  obtain ⟨c, htc, hUc⟩ := exists_Ico_subset_of_mem_nhds
    (hUopen.mem_nhds hU) ⟨t + 2, by
      have : (0 : ℝ≥0) < 1 := by norm_num
      have := add_lt_add_left this (t + 1)
      simpa [add_assoc] using this⟩
  intro a hta
  have hupper : t + 1 < min (a + 1) c := by
    exact lt_min (add_lt_add_left hta 1) htc
  obtain ⟨x, htx, hxupper⟩ := exists_between hupper
  let b : ℝ≥0 := x - 1
  have hone : 1 ≤ x := by
    calc
      (1 : ℝ≥0) ≤ t + 1 := by simpa [add_comm] using
        (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le) :
          1 ≤ 1 + t)
      _ ≤ x := htx.le
  have hbx : b + 1 = x := by
    dsimp [b]
    exact tsub_add_cancel_of_le hone
  have htb : t < b := by
    apply (add_lt_add_iff_right (1 : ℝ≥0)).mp
    rw [hbx]
    exact htx
  have hba : b < a := by
    apply (add_lt_add_iff_right (1 : ℝ≥0)).mp
    rw [hbx]
    exact hxupper.trans_le (min_le_left _ _)
  refine ⟨b, htb, hba, ?_⟩
  intro u hbu hub
  by_cases hu : u < t + 1
  · have htu : t < u := htb.trans_le hbu
    have htuEq : t + (u - t) = u := add_tsub_cancel_of_le htu.le
    rw [← htuEq]
    apply hinterior (u - t) (tsub_pos_iff_lt.mpr htu)
    exact (tsub_lt_iff_left htu.le).mpr (by simpa [add_comm] using hu)
  · have huc : u < c := (hub.trans_eq hbx).trans_lt
        (hxupper.trans_le (min_le_right _ _))
    exact hUc ⟨le_of_not_gt hu, huc⟩

/-- The deterministic continuity assertion in Bolthausen's Lemma 2.4.
The lower bound follows from compactness of possible starting times;
the upper bound uses the strict first window and the minimizer
construction above. -/
theorem continuousAt_firstNonnegativeWindowStart_of_strictWindow
    (f : C(ℝ≥0, ℝ)) (t : ℝ≥0)
    (hfirst : firstNonnegativeWindowStart f = t)
    (hinterior : ∀ u : ℝ≥0, 0 < u → u < 1 → f t < f (t + u))
    (hendpoint : f t < f (t + 1)) :
    ContinuousAt firstNonnegativeWindowStart f := by
  rw [continuousAt_iff_lower_upperSemicontinuousAt]
  exact ⟨lowerSemicontinuous_firstNonnegativeWindowStart.lowerSemicontinuousAt f,
    upperSemicontinuousAt_firstNonnegativeWindowStart_of_strictTails
      f t hfirst
      (strictUnitTails_of_strictInteriorAndEndpoint f t hinterior hendpoint)⟩

/-- Before the finite-horizon cutoff, the first eligible window is
the unrestricted first eligible window. -/
theorem firstNonnegativeWindowStartUpTo_eq_first_of_lt_cutoff
    (f : C(ℝ≥0, ℝ)) {s : ℝ≥0} (hs : 1 ≤ s)
    (hfirst : firstNonnegativeWindowStart f <
      (s - 1 : WithTop ℝ≥0)) :
    firstNonnegativeWindowStartUpTo f s = firstNonnegativeWindowStart f := by
  have hfinite : firstNonnegativeWindowStart f ≠ ⊤ :=
    (hfirst.trans (WithTop.coe_lt_top (s - 1))).ne
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have htd : t < s - 1 := WithTop.coe_lt_coe.mp (ht ▸ hfirst)
  have hts : t + 1 ≤ s := by
    have hsEq : s - 1 + 1 = s := tsub_add_cancel_of_le hs
    calc
      t + 1 ≤ (s - 1) + 1 := add_le_add_left htd.le 1
      _ = s := hsEq
  rw [← ht]
  exact firstNonnegativeWindowStartUpTo_eq_first_of_le f ht.symm hts

/-- Beyond the finite-horizon cutoff, there is no eligible unit
window wholly contained before $s$. -/
theorem firstNonnegativeWindowStartUpTo_eq_top_of_cutoff_lt
    (f : C(ℝ≥0, ℝ)) {s : ℝ≥0} (hs : 1 ≤ s)
    (hfirst : (s - 1 : WithTop ℝ≥0) <
      firstNonnegativeWindowStart f) :
    firstNonnegativeWindowStartUpTo f s = ⊤ := by
  by_contra hne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hrstart : firstNonnegativeWindowStartUpTo f s = r := hr.symm
  have hrs := (firstNonnegativeWindowStartUpTo_eq_coe_iff f s r).mp
    hrstart |>.1
  have hrd : r ≤ s - 1 := by
    have hsEq : s - 1 + 1 = s := tsub_add_cancel_of_le hs
    apply (add_le_add_iff_right (1 : ℝ≥0)).mp
    rw [hsEq]
    exact hrs
  have hle : firstNonnegativeWindowStart f ≤ (r : WithTop ℝ≥0) := by
    simpa [hrstart] using firstNonnegativeWindowStart_le_upTo f s
  exact (not_le_of_gt hfirst) (hle.trans (WithTop.coe_le_coe.mpr hrd))

/-- Passing from $T$ to $T^s$ introduces a possible discontinuity
only at the cutoff $s-1$. This is the reduction using Bolthausen's
equation (2.3) at the start of Lemma 2.4. -/
theorem continuousAt_firstNonnegativeWindowStartUpTo_of_ne_cutoff
    (f : C(ℝ≥0, ℝ)) {s : ℝ≥0} (hs : 1 ≤ s)
    (hcont : ContinuousAt firstNonnegativeWindowStart f)
    (hcut : firstNonnegativeWindowStart f ≠
      (s - 1 : WithTop ℝ≥0)) :
    ContinuousAt (fun g => firstNonnegativeWindowStartUpTo g s) f := by
  rcases lt_or_gt_of_ne hcut with hlt | hgt
  · have hnear : ∀ᶠ g in 𝓝 f,
        firstNonnegativeWindowStart g < (s - 1 : WithTop ℝ≥0) :=
      hcont.eventually (isOpen_Iio.mem_nhds hlt)
    apply hcont.congr_of_eventuallyEq
    filter_upwards [hnear] with g hg
    exact firstNonnegativeWindowStartUpTo_eq_first_of_lt_cutoff g hs hg
  · have hnear : ∀ᶠ g in 𝓝 f,
        (s - 1 : WithTop ℝ≥0) < firstNonnegativeWindowStart g :=
      hcont.eventually (isOpen_Ioi.mem_nhds hgt)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hnear] with g hg
    exact firstNonnegativeWindowStartUpTo_eq_top_of_cutoff_lt g hs hg

/-- A horizon shorter than one contains no full unit window. -/
theorem firstNonnegativeWindowStartUpTo_eq_top_of_lt_one
    (f : C(ℝ≥0, ℝ)) {s : ℝ≥0} (hs : s < 1) :
    firstNonnegativeWindowStartUpTo f s = ⊤ := by
  classical
  unfold firstNonnegativeWindowStartUpTo
  split_ifs with h
  · obtain ⟨t, hts, _⟩ := h
    have hone : (1 : ℝ≥0) ≤ t + 1 := by
      simpa [add_comm] using
        (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le) :
          1 ≤ 1 + t)
    exact False.elim ((not_le_of_gt hs) (hone.trans hts))
  · rfl

end ProbabilityTheory

end
