/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.ContinuousMap.LastZero
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Last sign change of a continuous path

The public definitions and theorems in this file are:

- `ContinuousMap.lastOppositeSign`: the supremum of times at which a
  path has sign opposite to its value at time one,
  $\sup\{t:f(t)f(1)<0\}$.
- `ContinuousMap.firstSignStableStart`: Bolthausen's earliest start of a
  tail whose values have one weak sign, positive or negative.
- `ContinuousMap.firstNoSignChangeStart`: the earliest start of a tail
  on which the path keeps the endpoint's weak sign,
  $\inf\{t:\forall s\ge t,\ f(s)f(1)\ge0\}$.
- `ContinuousMap.firstNoSignChangeStart_eq_lastOppositeSign`:
  the two endpoint-based definitions agree.
- `ContinuousMap.firstSignStableStart_eq_firstNoSignChangeStart_of_endpoint_ne_zero`:
  the original and endpoint-based start times agree when $f(1)\ne0$.
- `ContinuousMap.measurable_firstSignStableStart`:
  Bolthausen's original sign-stable start time is Borel measurable.
- `ContinuousMap.le_lastZero_of_opposite_sign`: $f(t)f(1)<0$
  implies $t\le g(f)$, where $g(f)$ is the last zero.
- `ContinuousMap.lastOppositeSign_le_lastZero`: the last opposite-sign
  time is no later than the last zero, $\tau'(f)\le g(f)$.
- `ContinuousMap.lastOppositeSign_eq_lastZero_of_approaches`:
  $\tau'(f)=g(f)$ if every $c<g(f)$ precedes some $t$ with
  $f(t)f(1)<0$.
- `ContinuousMap.isOpen_setOf_lt_lastOppositeSign`:
  $\{f:c<\tau'(f)\}$ is open.
- `ContinuousMap.measurable_firstNoSignChangeStart`:
  $f\mapsto\tau'(f)$ is Borel measurable.
- `ContinuousMap.continuousAt_firstNoSignChangeStart_of_eq_lastZero`:
  $f\mapsto\tau'(f)$ is continuous at each path satisfying
  $\tau'(f)=g(f)$.
- `ContinuousMap.lastSignChangeMeanderTransform`:
  the endpoint-sign version of
  $\Psi(f)(t)=|f(\tau'+(1-\tau')t)|/\sqrt{1-\tau'}$
  when $\tau'<1$; it agrees with Bolthausen's transform when $f(1)\ne0$.
- `ContinuousMap.signStableMeanderTransform`:
  the same formula using Bolthausen's original sign-stable start time.
- `ContinuousMap.measurable_signStableMeanderTransform`:
  the original path transform is Borel measurable.
- `ContinuousMap.measurable_lastSignChangeMeanderTransform`:
  $f\mapsto\Psi(f)$ is Borel measurable.
- `ContinuousMap.continuousAt_lastSignChangeMeanderTransform_of_eq_lastZero`:
  $f\mapsto\Psi(f)$ is continuous where $\tau'(f)=g(f)<1$.
- `ContinuousMap.lastSignChangeMeanderTransform_eq_lastZeroMeanderTransform`:
  $\Psi(f)=|f(g+(1-g)\cdot)|/\sqrt{1-g}$ under the same
  opposite-sign accumulation condition.

Bolthausen's original last-sign-change time is `firstSignStableStart`.
The endpoint-sign version differs only on paths ending at zero. The
functional is used in the sketch at the end of Erwin Bolthausen,
*On a functional central limit theorem for
random walks conditioned to stay positive*, Ann. Probab. 4(3) (1976),
480--485, page 484. The last-zero time is the one used in Donald L.
Iglehart, *Functional Central Limit Theorems for Random Walks Conditioned
to Stay Positive*, Ann. Probab. 2(4) (1974), 608--619, Section 3.
-/

@[expose] public section

namespace ContinuousMap

open Set

/-- Last time when a continuous path has sign opposite to its endpoint.
The supremum of the empty set is the start of the unit interval. -/
noncomputable def lastOppositeSign (f : C(unitInterval, ℝ)) : unitInterval :=
  sSup {t : unitInterval | f t * f ⊤ < 0}

/-- Earliest time from which the path never again takes sign opposite
to its endpoint. When the endpoint is nonzero this agrees with the
sign-stable tail time on page 484 of Bolthausen's article. -/
noncomputable def firstNoSignChangeStart
    (f : C(unitInterval, ℝ)) : unitInterval :=
  sInf {t : unitInterval | ∀ s : unitInterval,
    t ≤ s → 0 ≤ f s * f ⊤}

/-- The earliest time from which every later path value has one weak
sign. This is Bolthausen's original definition, including paths with
zero endpoint. -/
noncomputable def firstSignStableStart
    (f : C(unitInterval, ℝ)) : unitInterval :=
  sInf {t : unitInterval |
    (∀ s : unitInterval, t ≤ s → 0 ≤ f s) ∨
      (∀ s : unitInterval, t ≤ s → f s ≤ 0)}

/-- The source and endpoint-sign conventions agree whenever the path
ends away from zero. -/
theorem firstSignStableStart_eq_firstNoSignChangeStart_of_endpoint_ne_zero
    (f : C(unitInterval, ℝ)) (hend : f ⊤ ≠ 0) :
    firstSignStableStart f = firstNoSignChangeStart f := by
  have hset : {t : unitInterval |
      (∀ s : unitInterval, t ≤ s → 0 ≤ f s) ∨
        (∀ s : unitInterval, t ≤ s → f s ≤ 0)} =
      {t : unitInterval | ∀ s : unitInterval,
        t ≤ s → 0 ≤ f s * f ⊤} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    rcases lt_or_gt_of_ne hend with hneg | hpos
    · constructor
      · rintro (hpositive | hnegative) s hts
        · exact False.elim (not_le_of_gt hneg (hpositive ⊤ le_top))
        · exact mul_nonneg_of_nonpos_of_nonpos (hnegative s hts) hneg.le
      · intro h
        right
        intro s hts
        have hs := h s hts
        nlinarith
    · constructor
      · rintro (hpositive | hnegative) s hts
        · exact mul_nonneg (hpositive s hts) hpos.le
        · exact False.elim (not_le_of_gt hpos (hnegative ⊤ le_top))
      · intro h
        left
        intro s hts
        have hs := h s hts
        nlinarith
  simp only [firstSignStableStart, firstNoSignChangeStart, hset]

/-- The first stable-sign tail starts at the supremum of all preceding
opposite-sign times. -/
theorem firstNoSignChangeStart_eq_lastOppositeSign
    (f : C(unitInterval, ℝ)) :
    firstNoSignChangeStart f = lastOppositeSign f := by
  unfold firstNoSignChangeStart lastOppositeSign
  apply le_antisymm
  · by_contra hnot
    have hlt : sSup {t : unitInterval | f t * f ⊤ < 0} <
        sInf {t : unitInterval |
          ∀ s : unitInterval, t ≤ s → 0 ≤ f s * f ⊤} :=
      lt_of_not_ge hnot
    obtain ⟨u, hsup, hinf⟩ := exists_between hlt
    have hu : ∀ s : unitInterval, u ≤ s → 0 ≤ f s * f ⊤ := by
      intro s hus
      by_contra hneg
      have hsn : f s * f ⊤ < 0 := lt_of_not_ge hneg
      exact (not_le_of_gt hsup) (hus.trans (le_sSup hsn))
    exact (not_le_of_gt hinf) (sInf_le hu)
  · apply sSup_le
    intro t ht
    apply le_sInf
    intro u hu
    by_contra hnot
    have hut : u ≤ t := le_of_lt (lt_of_not_ge hnot)
    exact (not_le_of_gt ht) (hu t hut)

/-- Every point with sign opposite to the endpoint precedes a zero of
the path. -/
theorem le_lastZero_of_opposite_sign (f : C(unitInterval, ℝ))
    {t : unitInterval} (ht : f t * f ⊤ < 0) :
    t ≤ lastZero f := by
  let g : unitInterval → ℝ := fun s => f s * f ⊤
  have hgcont : Continuous g := f.continuous.mul continuous_const
  have hlast : 0 ≤ g ⊤ := by
    change 0 ≤ f ⊤ * f ⊤
    nlinarith [sq_nonneg (f ⊤)]
  obtain ⟨s, hs, hsg⟩ :=
    (intermediate_value_Icc (le_top : t ≤ ⊤) hgcont.continuousOn)
      (show (0 : ℝ) ∈ Icc (g t) (g ⊤) from ⟨ht.le, hlast⟩)
  have hfend : f ⊤ ≠ 0 := by
    intro h
    simp [h] at ht
  have hzero : f s = 0 := by
    have hmul : f s * f ⊤ = 0 := hsg
    exact (mul_eq_zero.mp hmul).resolve_right hfend
  exact hs.1.trans (le_lastZero_of_apply_eq_zero f hzero)

/-- The last opposite-sign time is bounded above by the last zero. -/
theorem lastOppositeSign_le_lastZero (f : C(unitInterval, ℝ)) :
    lastOppositeSign f ≤ lastZero f := by
  unfold lastOppositeSign
  exact sSup_le fun t ht => le_lastZero_of_opposite_sign f ht

/-- Opposite-sign values arbitrarily near the last zero identify the
last-sign-change and last-zero times. -/
theorem lastOppositeSign_eq_lastZero_of_approaches
    (f : C(unitInterval, ℝ))
    (happroach : ∀ c : unitInterval, c < lastZero f →
      ∃ t : unitInterval, c < t ∧ f t * f ⊤ < 0) :
    lastOppositeSign f = lastZero f := by
  apply le_antisymm (lastOppositeSign_le_lastZero f)
  by_contra hnot
  have hlt : lastOppositeSign f < lastZero f := lt_of_not_ge hnot
  obtain ⟨t, hct, ht⟩ := happroach (lastOppositeSign f) hlt
  exact (not_le_of_gt hct) (le_sSup ht)

/-- The paths whose last opposite-sign time is after a fixed time
form an open set. -/
theorem isOpen_setOf_lt_lastOppositeSign (c : unitInterval) :
    IsOpen {f : C(unitInterval, ℝ) | c < lastOppositeSign f} := by
  let Z : Set (C(unitInterval, ℝ) × unitInterval) :=
    {p | c < p.2 ∧ p.1 p.2 * p.1 ⊤ < 0}
  have hprod : Continuous
      (fun p : C(unitInterval, ℝ) × unitInterval => p.1 p.2 * p.1 ⊤) :=
    continuous_eval.mul
      ((continuous_eval_const ⊤).comp continuous_fst)
  have hZopen : IsOpen Z :=
    (isOpen_Ioi.preimage continuous_snd).inter
      (isOpen_Iio.preimage hprod)
  have himage :
      {f : C(unitInterval, ℝ) | c < lastOppositeSign f} =
        Prod.fst '' Z := by
    ext f
    constructor
    · intro hf
      change c < sSup {t : unitInterval | f t * f ⊤ < 0} at hf
      obtain ⟨t, ht, hct⟩ := lt_sSup_iff.mp hf
      exact ⟨⟨f, t⟩, ⟨hct, ht⟩, rfl⟩
    · rintro ⟨⟨g, t⟩, ⟨hct, ht⟩, rfl⟩
      change c < sSup {u : unitInterval | g u * g ⊤ < 0}
      exact lt_sSup_iff.mpr ⟨t, ht, hct⟩
  rw [himage]
  exact isOpenMap_fst Z hZopen

/-- The first stable-sign tail time is Borel measurable. -/
theorem measurable_firstNoSignChangeStart :
    Measurable (firstNoSignChangeStart :
      C(unitInterval, ℝ) → unitInterval) := by
  rw [show firstNoSignChangeStart = lastOppositeSign from
    funext firstNoSignChangeStart_eq_lastOppositeSign]
  apply measurable_of_Ioi
  intro c
  exact (isOpen_setOf_lt_lastOppositeSign c).measurableSet

private theorem firstAvoidanceStart_eq_lastOccurrence
    (P : unitInterval → Prop) :
    sInf {t : unitInterval | ∀ s : unitInterval, t ≤ s → ¬ P s} =
      sSup {t : unitInterval | P t} := by
  apply le_antisymm
  · by_contra hnot
    have hlt : sSup {t : unitInterval | P t} <
        sInf {t : unitInterval | ∀ s, t ≤ s → ¬ P s} :=
      lt_of_not_ge hnot
    obtain ⟨u, hsup, hinf⟩ := exists_between hlt
    have hu : ∀ s : unitInterval, u ≤ s → ¬ P s := by
      intro s hus hs
      exact (not_le_of_gt hsup) (hus.trans (le_sSup hs))
    exact (not_le_of_gt hinf) (sInf_le hu)
  · apply sSup_le
    intro t ht
    apply le_sInf
    intro u hu
    by_contra hnot
    have hut : u ≤ t := le_of_lt (lt_of_not_ge hnot)
    exact (hu t hut) ht

private noncomputable def lastNegative (f : C(unitInterval, ℝ)) : unitInterval :=
  sSup {t : unitInterval | f t < 0}

private noncomputable def lastPositive (f : C(unitInterval, ℝ)) : unitInterval :=
  sSup {t : unitInterval | 0 < f t}

private theorem firstSignStableStart_eq_min (f : C(unitInterval, ℝ)) :
    firstSignStableStart f = min (lastNegative f) (lastPositive f) := by
  have hset : {t : unitInterval |
      (∀ s : unitInterval, t ≤ s → 0 ≤ f s) ∨
        (∀ s : unitInterval, t ≤ s → f s ≤ 0)} =
      {t : unitInterval | ∀ s : unitInterval, t ≤ s → ¬ f s < 0} ∪
        {t : unitInterval | ∀ s : unitInterval, t ≤ s → ¬ 0 < f s} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (fun s hts hs => not_lt_of_ge (h s hts) hs)
      · exact Or.inr (fun s hts hs => not_lt_of_ge (h s hts) hs)
    · rintro (h | h)
      · exact Or.inl (fun s hts => le_of_not_gt (h s hts))
      · exact Or.inr (fun s hts => le_of_not_gt (h s hts))
  rw [firstSignStableStart, hset, sInf_union]
  rw [firstAvoidanceStart_eq_lastOccurrence,
    firstAvoidanceStart_eq_lastOccurrence]
  rfl

private theorem isOpen_setOf_lt_lastOccurrence
    (c : unitInterval) (Z : Set (C(unitInterval, ℝ) × unitInterval))
    (hZ : IsOpen Z) :
    IsOpen {f : C(unitInterval, ℝ) |
      c < sSup {t : unitInterval | (f, t) ∈ Z}} := by
  let U : Set (C(unitInterval, ℝ) × unitInterval) :=
    {p | c < p.2} ∩ Z
  have hU : IsOpen U :=
    (isOpen_Ioi.preimage continuous_snd).inter hZ
  have himage : {f : C(unitInterval, ℝ) |
      c < sSup {t : unitInterval | (f, t) ∈ Z}} = Prod.fst '' U := by
    ext f
    constructor
    · intro hf
      change c < sSup {t : unitInterval | (f, t) ∈ Z} at hf
      obtain ⟨t, ht, hct⟩ := lt_sSup_iff.mp hf
      exact ⟨⟨f, t⟩, ⟨hct, ht⟩, rfl⟩
    · rintro ⟨⟨g, t⟩, ⟨hct, ht⟩, rfl⟩
      exact lt_sSup_iff.mpr ⟨t, ht, hct⟩
  rw [himage]
  exact isOpenMap_fst U hU

private theorem measurable_lastNegative : Measurable lastNegative := by
  apply measurable_of_Ioi
  intro c
  have hZ : IsOpen {p : C(unitInterval, ℝ) × unitInterval |
      p.1 p.2 < 0} := by
    convert ((isOpen_Iio : IsOpen (Set.Iio (0 : ℝ))).preimage
      (continuous_eval : Continuous
      (fun p : C(unitInterval, ℝ) × unitInterval => p.1 p.2))) using 1
    ext p
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_ofPred_eq]
  exact (isOpen_setOf_lt_lastOccurrence c _ hZ).measurableSet

private theorem measurable_lastPositive : Measurable lastPositive := by
  apply measurable_of_Ioi
  intro c
  have hZ : IsOpen {p : C(unitInterval, ℝ) × unitInterval |
      0 < p.1 p.2} := by
    convert ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage
      (continuous_eval : Continuous
      (fun p : C(unitInterval, ℝ) × unitInterval => p.1 p.2))) using 1
    ext p
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq]
  exact (isOpen_setOf_lt_lastOccurrence c _ hZ).measurableSet

/-- The first sign-stable tail time is Borel measurable. It is the
minimum of the last strictly negative and last strictly positive times. -/
theorem measurable_firstSignStableStart : Measurable firstSignStableStart := by
  rw [show firstSignStableStart = fun f =>
    min (lastNegative f) (lastPositive f) from
      funext firstSignStableStart_eq_min]
  exact measurable_lastNegative.min measurable_lastPositive

/-- The last opposite-sign time is continuous at a path where it agrees
with the last zero. Lower continuity follows from the open opposite-sign
event, and upper continuity from the closed last-zero event. -/
theorem continuousAt_firstNoSignChangeStart_of_eq_lastZero
    (f : C(unitInterval, ℝ))
    (heq : firstNoSignChangeStart f = lastZero f) :
    ContinuousAt firstNoSignChangeStart f := by
  rw [ContinuousAt, tendsto_order]
  constructor
  · intro c hc
    have hopen : IsOpen {g : C(unitInterval, ℝ) |
        c < firstNoSignChangeStart g} := by
      simpa only [firstNoSignChangeStart_eq_lastOppositeSign] using
        isOpen_setOf_lt_lastOppositeSign c
    exact hopen.mem_nhds hc
  · intro c hc
    have hclosed : IsClosed {g : C(unitInterval, ℝ) |
        c ≤ lastZero g} := isClosed_setOf_le_lastZero c
    have hmem : {g : C(unitInterval, ℝ) | lastZero g < c} ∈ nhds f := by
      have hopen : IsOpen {g : C(unitInterval, ℝ) | lastZero g < c} := by
        convert hclosed.isOpen_compl using 1
        ext g
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      exact hopen.mem_nhds (by simpa only [Set.mem_ofPred_eq, ← heq] using hc)
    filter_upwards [hmem] with g hg
    calc
      firstNoSignChangeStart g = lastOppositeSign g :=
        firstNoSignChangeStart_eq_lastOppositeSign g
      _ ≤ lastZero g := lastOppositeSign_le_lastZero g
      _ < c := hg

/-- The endpoint-sign terminal path, rescaled to unit duration;
the endpoint case is assigned the zero path. -/
noncomputable def lastSignChangeMeanderTransform
    (f : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  ⟨(fun t => if firstNoSignChangeStart f = ⊤ then 0 else
      |f (tailAffineTime (firstNoSignChangeStart f) t)| /
        Real.sqrt (1 - (firstNoSignChangeStart f : ℝ))), by
    by_cases h : firstNoSignChangeStart f = ⊤
    · simp only [h, ↓reduceIte]
      exact continuous_const
    · simp only [h, ↓reduceIte]
      exact ((f.continuous.comp
        (continuous_tailAffineTime (firstNoSignChangeStart f))).abs).div_const _⟩

/-- Bolthausen's original terminal-sign-stable transform. Its start
time observes both possible weak signs, including paths ending at zero. -/
noncomputable def signStableMeanderTransform
    (f : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  ⟨(fun t => if firstSignStableStart f = ⊤ then 0 else
      |f (tailAffineTime (firstSignStableStart f) t)| /
        Real.sqrt (1 - (firstSignStableStart f : ℝ))), by
    by_cases h : firstSignStableStart f = ⊤
    · simp only [h, ↓reduceIte]
      exact continuous_const
    · simp only [h, ↓reduceIte]
      exact ((f.continuous.comp
        (continuous_tailAffineTime (firstSignStableStart f))).abs).div_const _⟩

/-- The original and endpoint-sign transforms coincide at every
path whose endpoint is nonzero. -/
theorem signStableMeanderTransform_eq_lastSignChangeMeanderTransform
    (f : C(unitInterval, ℝ)) (hend : f ⊤ ≠ 0) :
    signStableMeanderTransform f = lastSignChangeMeanderTransform f := by
  simp only [signStableMeanderTransform, lastSignChangeMeanderTransform,
    firstSignStableStart_eq_firstNoSignChangeStart_of_endpoint_ne_zero f hend]

/-- The endpoint-sign rescaled transform is Borel measurable as a
continuous-path-valued map. -/
theorem measurable_lastSignChangeMeanderTransform :
    Measurable (lastSignChangeMeanderTransform :
      C(unitInterval, ℝ) → C(unitInterval, ℝ)) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  have htime : Measurable
      (fun f : C(unitInterval, ℝ) =>
        tailAffineTime (firstNoSignChangeStart f) t) :=
    (continuous_tailAffineTime_left t).measurable.comp
      measurable_firstNoSignChangeStart
  have heval : Measurable
      (fun f : C(unitInterval, ℝ) =>
        f (tailAffineTime (firstNoSignChangeStart f) t)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk htime)
  have hdenom : Measurable
      (fun f : C(unitInterval, ℝ) =>
        Real.sqrt (1 - (firstNoSignChangeStart f : ℝ))) :=
    Real.continuous_sqrt.measurable.comp
      (measurable_const.sub
        (continuous_subtype_val.measurable.comp
          measurable_firstNoSignChangeStart))
  change Measurable (fun f : C(unitInterval, ℝ) =>
    if firstNoSignChangeStart f = ⊤ then 0 else
      |f (tailAffineTime (firstNoSignChangeStart f) t)| /
        Real.sqrt (1 - (firstNoSignChangeStart f : ℝ)))
  have hset : MeasurableSet
      {f : C(unitInterval, ℝ) | firstNoSignChangeStart f = ⊤} :=
    measurable_firstNoSignChangeStart (measurableSet_singleton ⊤)
  exact Measurable.ite hset measurable_const
    ((continuous_abs.measurable.comp heval).div hdenom)

/-- Bolthausen's original sign-stable path transform is Borel
measurable as a continuous-path-valued map. -/
theorem measurable_signStableMeanderTransform :
    Measurable (signStableMeanderTransform :
      C(unitInterval, ℝ) → C(unitInterval, ℝ)) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  have htime : Measurable
      (fun f : C(unitInterval, ℝ) =>
        tailAffineTime (firstSignStableStart f) t) :=
    (continuous_tailAffineTime_left t).measurable.comp
      measurable_firstSignStableStart
  have heval : Measurable
      (fun f : C(unitInterval, ℝ) =>
        f (tailAffineTime (firstSignStableStart f) t)) :=
    continuous_eval.measurable.comp (measurable_id.prodMk htime)
  have hdenom : Measurable
      (fun f : C(unitInterval, ℝ) =>
        Real.sqrt (1 - (firstSignStableStart f : ℝ))) :=
    Real.continuous_sqrt.measurable.comp
      (measurable_const.sub
        (continuous_subtype_val.measurable.comp
          measurable_firstSignStableStart))
  change Measurable (fun f : C(unitInterval, ℝ) =>
    if firstSignStableStart f = ⊤ then 0 else
      |f (tailAffineTime (firstSignStableStart f) t)| /
        Real.sqrt (1 - (firstSignStableStart f : ℝ)))
  have hset : MeasurableSet
      {f : C(unitInterval, ℝ) | firstSignStableStart f = ⊤} :=
    measurable_firstSignStableStart (measurableSet_singleton ⊤)
  exact Measurable.ite hset measurable_const
    ((continuous_abs.measurable.comp heval).div hdenom)

private abbrev nonterminalStart := {start : unitInterval // start < ⊤}

private noncomputable def rescaledTailAt
    (f : C(unitInterval, ℝ)) (start : nonterminalStart) :
    C(unitInterval, ℝ) :=
  ⟨fun t => |f (tailAffineTime start.1 t)| /
    Real.sqrt (1 - (start.1 : ℝ)),
    ((f.continuous.comp (continuous_tailAffineTime start.1)).abs).div_const _⟩

private theorem continuous_tailAffineTime_pair :
    Continuous (fun p : unitInterval × unitInterval =>
      tailAffineTime p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : unitInterval × unitInterval =>
    (p.1 : ℝ) + (1 - (p.1 : ℝ)) * (p.2 : ℝ))
  fun_prop

private theorem continuous_rescaledTailAt :
    Continuous (fun p : C(unitInterval, ℝ) × nonterminalStart =>
      rescaledTailAt p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have htime : Continuous (fun p :
      (C(unitInterval, ℝ) × nonterminalStart) × unitInterval =>
      tailAffineTime p.1.2.1 p.2) :=
    continuous_tailAffineTime_pair.comp
      ((continuous_subtype_val.comp
        (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have heval : Continuous (fun p :
      (C(unitInterval, ℝ) × nonterminalStart) × unitInterval =>
      p.1.1 (tailAffineTime p.1.2.1 p.2)) :=
    continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk htime)
  have hdenom : Continuous (fun p :
      (C(unitInterval, ℝ) × nonterminalStart) × unitInterval =>
      Real.sqrt (1 - (p.1.2.1 : ℝ))) := by fun_prop
  have hdenom_ne (p :
      (C(unitInterval, ℝ) × nonterminalStart) × unitInterval) :
      Real.sqrt (1 - (p.1.2.1 : ℝ)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    exact sub_pos.mpr (by exact_mod_cast p.1.2.2)
  exact heval.abs.div hdenom hdenom_ne

/-- The endpoint-sign terminal-path transform is continuous at a path whose
last sign change equals its last zero and precedes time one. -/
theorem continuousAt_lastSignChangeMeanderTransform_of_eq_lastZero
    (f : C(unitInterval, ℝ))
    (heq : firstNoSignChangeStart f = lastZero f)
    (hlt : lastZero f < ⊤) :
    ContinuousAt lastSignChangeMeanderTransform f := by
  classical
  let start : C(unitInterval, ℝ) → nonterminalStart := fun g =>
    if h : firstNoSignChangeStart g < ⊤ then
      ⟨firstNoSignChangeStart g, h⟩ else ⟨0, bot_lt_top⟩
  have hτcont := continuousAt_firstNoSignChangeStart_of_eq_lastZero f heq
  have hevent : ∀ᶠ g in nhds f, firstNoSignChangeStart g < ⊤ :=
    hτcont.eventually (isOpen_Iio.mem_nhds (heq ▸ hlt))
  have hval : ContinuousAt (fun g => (start g : unitInterval)) f := by
    apply hτcont.congr
    filter_upwards [hevent] with g hg
    simp [start, hg]
  have hstart : ContinuousAt start f := by
    exact (continuousAt_codRestrict_iff (fun g => (start g).2)).mpr hval
  have hrescale : ContinuousAt
      (fun g => rescaledTailAt g (start g)) f :=
    continuous_rescaledTailAt.continuousAt.comp
      (continuousAt_id.prodMk hstart)
  apply hrescale.congr
  filter_upwards [hevent] with g hg
  simp only [start, hg, dite_true, rescaledTailAt,
    lastSignChangeMeanderTransform]
  apply ContinuousMap.ext
  intro t
  simp [hg.ne]

/-- On paths with opposite-sign values arbitrarily close to the last
zero, Bolthausen's terminal segment is Iglehart's last-zero segment. -/
theorem lastSignChangeMeanderTransform_eq_lastZeroMeanderTransform
    (f : C(unitInterval, ℝ))
    (happroach : ∀ c : unitInterval, c < lastZero f →
      ∃ t : unitInterval, c < t ∧ f t * f ⊤ < 0) :
    lastSignChangeMeanderTransform f = lastZeroMeanderTransform f := by
  simp only [lastSignChangeMeanderTransform, lastZeroMeanderTransform,
    firstNoSignChangeStart_eq_lastOppositeSign,
    lastOppositeSign_eq_lastZero_of_approaches f happroach]

end ContinuousMap

end
