/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.ContinuousMap
public import Topology.Cadlag.Skorokhod.Corridor
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.PathClass.Boundary
import Mathlib.Topology.Semicontinuity.Michael

/-!
# Mogul'skii path classes `M₁` and `M₂`

This is the statement layer for the path classes in §1 of A. A. Mogul'skii,
"Small deviations in the space of trajectories" (1974). `M₁` consists of
strict corridors between finite right-continuous step boundaries, and `M₂`
adds nonempty intersection with continuous paths. The source's two-sided
trace-separation condition is proved equivalent to this nonemptiness, with a
separate start condition because paths are pinned to zero. Endpoint traces use
the convention defined in `PathClass.Boundary`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

@[expose] public section

/-! ## Corridors in `M₂` -/

namespace ProbabilityTheory.RandomWalk.SmallDeviation

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

/-- A finite extended-real interval, viewed as a subset of `ℝ`, is convex.
This lets the continuous-selection argument handle finite and infinite step
levels uniformly. -/
private lemma real_weighted_sum_gt {l x y a b : ℝ} (hx : l < x) (hy : l < y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : l < a * x + b * y := by
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by rw [ha0, zero_add] at hab; exact hab
    rw [ha0, hb1]; simpa using hy
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hpos : 0 < a * (x - l) + b * (y - l) :=
      add_pos_of_pos_of_nonneg (mul_pos hap (sub_pos.mpr hx))
        (mul_nonneg hb (le_of_lt (sub_pos.mpr hy)))
    have heq : a * x + b * y = l + (a * (x-l) + b * (y-l)) := by
      calc
        a * x + b * y = (a+b)*l + (a*(x-l)+b*(y-l)) := by ring
        _ = l + (a*(x-l)+b*(y-l)) := by rw [hab]; ring
    rw [heq]; linarith

private lemma real_weighted_sum_lt {x y u a b : ℝ} (hx : x < u) (hy : y < u)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a * x + b * y < u := by
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by rw [ha0, zero_add] at hab; exact hab
    rw [ha0, hb1]; simpa using hy
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hpos : 0 < a * (u - x) + b * (u - y) :=
      add_pos_of_pos_of_nonneg (mul_pos hap (sub_pos.mpr hx))
        (mul_nonneg hb (le_of_lt (sub_pos.mpr hy)))
    have heq : u - (a * x + b * y) = a * (u-x) + b * (u-y) := by
      calc
        u - (a*x+b*y) = (a+b)*u - (a*x+b*y) := by rw [hab]; ring
        _ = a*(u-x)+b*(u-y) := by ring
    rw [← sub_pos]; rw [heq]; exact hpos

private lemma convex_ereal_interval (l u : EReal) :
    Convex ℝ {x : ℝ | l < (x : EReal) ∧ (x : EReal) < u} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  constructor
  · by_cases hlbot : l = ⊥
    · subst l; exact EReal.bot_lt_coe _
    · by_cases hltop : l = ⊤
      · subst l; exact (lt_asymm hx.1 (EReal.coe_lt_top x)).elim
      · have hle : (l.toReal : EReal) = l := EReal.coe_toReal hltop hlbot
        have hxR : l.toReal < x := by
          apply EReal.coe_lt_coe_iff.mp; simpa [hle] using hx.1
        have hyR : l.toReal < y := by
          apply EReal.coe_lt_coe_iff.mp; simpa [hle] using hy.1
        rw [← hle, EReal.coe_lt_coe_iff]
        simpa only [smul_eq_mul] using real_weighted_sum_gt hxR hyR ha hb hab
  · by_cases hutop : u = ⊤
    · subst u; exact EReal.coe_lt_top _
    · by_cases hubot : u = ⊥
      · subst u; exact (lt_asymm (EReal.bot_lt_coe x) hx.2).elim
      · have hle : (u.toReal : EReal) = u := EReal.coe_toReal hutop hubot
        have hxR : x < u.toReal := by
          apply EReal.coe_lt_coe_iff.mp; simpa [hle] using hx.2
        have hyR : y < u.toReal := by
          apply EReal.coe_lt_coe_iff.mp; simpa [hle] using hy.2
        rw [← hle, EReal.coe_lt_coe_iff]
        simpa only [smul_eq_mul] using real_weighted_sum_lt hxR hyR ha hb hab

noncomputable def selValues (upper lower : StepBoundary) (t : unitInterval) : Set ℝ :=
  {x | max (lower.leftTrace t) (lower.rightTrace t) < (x : EReal) ∧
    (x : EReal) < min (upper.leftTrace t) (upper.rightTrace t)}

private lemma mem_selValues_iff {upper lower : StepBoundary}
    {t : unitInterval} (x : ℝ) :
    x ∈ selValues upper lower t ↔
      lower.leftTrace t < (x : EReal) ∧ lower.rightTrace t < (x : EReal) ∧
      (x : EReal) < upper.leftTrace t ∧ (x : EReal) < upper.rightTrace t := by
  constructor
  · intro h
    rcases max_lt_iff.mp h.1 with ⟨hL, hR⟩
    rcases lt_min_iff.mp h.2 with ⟨hU, hV⟩
    exact ⟨hL, hR, hU, hV⟩
  · rintro ⟨hL, hR, hU, hV⟩
    exact ⟨max_lt_iff.mpr ⟨hL, hR⟩, lt_min_iff.mpr ⟨hU, hV⟩⟩

private lemma selValues_nonempty {upper lower : StepBoundary}
    (hsep : TraceSeparated upper lower) (t : unitInterval) :
    (selValues upper lower t).Nonempty := by
  obtain ⟨x, hxlo, hxhi⟩ := EReal.exists_between_coe_real (hsep t)
  refine ⟨x, ?_⟩
  rw [mem_selValues_iff]
  exact ⟨lt_of_le_of_lt (le_max_left _ _) hxlo,
    lt_of_le_of_lt (le_max_right _ _) hxlo,
    lt_of_lt_of_le hxhi (min_le_left _ _),
    lt_of_lt_of_le hxhi (min_le_right _ _)⟩

private lemma selValues_convex (upper lower : StepBoundary) (t : unitInterval) :
    Convex ℝ (selValues upper lower t) := by
  simpa only [selValues, Set.mem_ofPred_eq] using
    convex_ereal_interval (max (lower.leftTrace t) (lower.rightTrace t))
      (min (upper.leftTrace t) (upper.rightTrace t))

private lemma not_mem_of_left_gap {knots : Finset unitInterval} {b : StepBoundary}
    (hsub : b.knots ⊆ knots) {p s t : unitInterval}
    (hp : p < s) (hst : s < t)
    (hgap : ∀ r ∈ knots, r < t → r ≤ p) : s ∉ b.knots := by
  intro hs
  have hrs := hgap s (hsub hs) hst
  exact (not_le_of_gt hp) hrs

private lemma not_mem_of_right_gap {knots : Finset unitInterval} {b : StepBoundary}
    (hsub : b.knots ⊆ knots) {t s q : unitInterval}
    (hts : t < s) (hsq : s < q)
    (hgap : ∀ r ∈ knots, t < r → q ≤ r) : s ∉ b.knots := by
  intro hs
  have hrs := hgap s (hsub hs) hts
  exact (not_le_of_gt hsq) hrs

private lemma selValues_openLowerSections {upper lower : StepBoundary} :
    HasOpenLowerSections (selValues upper lower) := by
  rw [hasOpenLowerSections_iff_isOpen]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro t ht
  let knots := lower.knots ∪ upper.knots
  have hsubL : lower.knots ⊆ knots := by
    intro r hr; exact Finset.mem_union.mpr (Or.inl hr)
  have hsubU : upper.knots ⊆ knots := by
    intro r hr; exact Finset.mem_union.mpr (Or.inr hr)
  have hfour := (mem_selValues_iff x).mp ht
  by_cases hbot : t = ⊥
  · subst t
    obtain ⟨q, hq, hqgap⟩ := StepBoundary.exists_right_gap_finset knots
      (show (⊥ : unitInterval) < ⊤ by norm_num)
    refine mem_of_superset (Iio_mem_nhds hq) ?_
    intro s hs
    by_cases hsbot : s = ⊥
    · subst s; change x ∈ selValues upper lower ⊥ at ht; exact ht
    · have hpos : ⊥ < s := bot_lt_iff_ne_bot.mpr hsbot
      have hnoL : ∀ r ∈ lower.knots, r ≤ s → False := by
        intro r hr hrs
        have hrbot : r ≠ ⊥ := by
          intro heq; subst r; exact lower.noBotKnot hr
        have hrpos : ⊥ < r := bot_lt_iff_ne_bot.mpr hrbot
        have hqr := hqgap r (hsubL hr) hrpos
        exact (not_le_of_gt hs) (hqr.trans hrs)
      have hnoU : ∀ r ∈ upper.knots, r ≤ s → False := by
        intro r hr hrs
        have hrbot : r ≠ ⊥ := by
          intro heq; subst r; exact upper.noBotKnot hr
        have hrpos : ⊥ < r := bot_lt_iff_ne_bot.mpr hrbot
        have hqr := hqgap r (hsubU hr) hrpos
        exact (not_le_of_gt hs) (hqr.trans hrs)
      have hidxL : lower.eval s = lower.eval ⊥ := by
        have hsq : s < q := hs
        rw [← StepBoundary.rightTrace_eq_eval lower ⊥]
        exact StepBoundary.eval_eq_rightTrace_of_between lower hpos hsq
          (fun r hr hrpos => hqgap r (hsubL hr) hrpos)
      have hidxU : upper.eval s = upper.eval ⊥ := by
        have hsq : s < q := hs
        rw [← StepBoundary.rightTrace_eq_eval upper ⊥]
        exact StepBoundary.eval_eq_rightTrace_of_between upper hpos hsq
          (fun r hr hrpos => hqgap r (hsubU hr) hrpos)
      have hnotL : s ∉ lower.knots := by
        intro hr; exact hnoL s hr le_rfl
      have hnotU : s ∉ upper.knots := by
        intro hr; exact hnoU s hr le_rfl
      have htraceL : lower.leftTrace s = lower.eval ⊥ := by
        rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem lower hnotL,
          StepBoundary.rightTrace_eq_eval, hidxL]
      have htraceU : upper.leftTrace s = upper.eval ⊥ := by
        rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem upper hnotU,
          StepBoundary.rightTrace_eq_eval, hidxU]
      have hfourBot : lower.eval ⊥ < (x : EReal) ∧ lower.eval ⊥ < (x : EReal) ∧
          (x : EReal) < upper.eval ⊥ ∧ (x : EReal) < upper.eval ⊥ := by
        simpa [StepBoundary.leftTrace_bot, StepBoundary.rightTrace_eq_eval] using hfour
      change x ∈ selValues upper lower s
      rw [mem_selValues_iff]
      exact ⟨by rw [htraceL]; exact hfourBot.1,
        by rw [StepBoundary.rightTrace_eq_eval, hidxL]; exact hfourBot.2.1,
        by rw [htraceU]; exact hfourBot.2.2.1,
        by rw [StepBoundary.rightTrace_eq_eval, hidxU]; exact hfourBot.2.2.2⟩
  · have htpos : ⊥ < t := bot_lt_iff_ne_bot.mpr hbot
    by_cases htop : t = ⊤
    · subst t
      obtain ⟨p, hp, hpgap⟩ := StepBoundary.exists_left_gap_finset knots
        (show (⊥ : unitInterval) < ⊤ by norm_num)
      refine mem_of_superset (Ioi_mem_nhds hp) ?_
      intro s hs
      by_cases hstop : s = ⊤
      · subst s; change x ∈ selValues upper lower ⊤ at ht; exact ht
      · have hst : s < ⊤ := lt_top_iff_ne_top.mpr hstop
        have hnotL : s ∉ lower.knots :=
          not_mem_of_left_gap hsubL hs hst hpgap
        have hnotU : s ∉ upper.knots :=
          not_mem_of_left_gap hsubU hs hst hpgap
        have hevalL : lower.eval s = lower.leftTrace ⊤ :=
          StepBoundary.eval_eq_leftTrace_of_between lower hs hst
            (fun r hr hrTop => hpgap r (hsubL hr) hrTop)
        have hevalU : upper.eval s = upper.leftTrace ⊤ :=
          StepBoundary.eval_eq_leftTrace_of_between upper hs hst
            (fun r hr hrTop => hpgap r (hsubU hr) hrTop)
        have hleftL : lower.leftTrace s = lower.leftTrace ⊤ := by
          rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem lower hnotL,
            StepBoundary.rightTrace_eq_eval, hevalL]
        have hleftU : upper.leftTrace s = upper.leftTrace ⊤ := by
          rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem upper hnotU,
            StepBoundary.rightTrace_eq_eval, hevalU]
        change x ∈ selValues upper lower s
        rw [mem_selValues_iff]
        exact ⟨by rw [hleftL]; exact hfour.1,
          by rw [StepBoundary.rightTrace_eq_eval, hevalL]; exact hfour.1,
          by rw [hleftU]; exact hfour.2.2.1,
          by rw [StepBoundary.rightTrace_eq_eval, hevalU]; exact hfour.2.2.1⟩
    · have httop : t < ⊤ := lt_top_iff_ne_top.mpr htop
      obtain ⟨p, hpt, hpleft⟩ := StepBoundary.exists_left_gap_finset knots htpos
      obtain ⟨q, htq, hqright⟩ := StepBoundary.exists_right_gap_finset knots httop
      refine mem_of_superset (Ioo_mem_nhds hpt htq) ?_
      intro s hs
      by_cases hst : s = t
      · subst s; change x ∈ selValues upper lower t at ht; exact ht
      · by_cases hleft : s < t
        · have hnotL : s ∉ lower.knots :=
            not_mem_of_left_gap hsubL hs.1 hleft hpleft
          have hnotU : s ∉ upper.knots :=
            not_mem_of_left_gap hsubU hs.1 hleft hpleft
          have hevalL : lower.eval s = lower.leftTrace t :=
            StepBoundary.eval_eq_leftTrace_of_between lower hs.1 hleft
              (fun r hr hrt => hpleft r (hsubL hr) hrt)
          have hevalU : upper.eval s = upper.leftTrace t :=
            StepBoundary.eval_eq_leftTrace_of_between upper hs.1 hleft
              (fun r hr hrt => hpleft r (hsubU hr) hrt)
          have hleftL : lower.leftTrace s = lower.leftTrace t := by
            rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem lower hnotL,
              StepBoundary.rightTrace_eq_eval, hevalL]
          have hleftU : upper.leftTrace s = upper.leftTrace t := by
            rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem upper hnotU,
              StepBoundary.rightTrace_eq_eval, hevalU]
          apply (mem_selValues_iff x).2
          exact ⟨by rw [hleftL]; exact hfour.1,
            by rw [StepBoundary.rightTrace_eq_eval, hevalL]; exact hfour.1,
            by rw [hleftU]; exact hfour.2.2.1,
            by rw [StepBoundary.rightTrace_eq_eval, hevalU]; exact hfour.2.2.1⟩
        · have hts : t < s := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hst)
          have hnotL : s ∉ lower.knots :=
            not_mem_of_right_gap hsubL hts hs.2 hqright
          have hnotU : s ∉ upper.knots :=
            not_mem_of_right_gap hsubU hts hs.2 hqright
          have hevalL : lower.eval s = lower.rightTrace t :=
            StepBoundary.eval_eq_rightTrace_of_between lower hts hs.2
              (fun r hr hrt => hqright r (hsubL hr) hrt)
          have hevalU : upper.eval s = upper.rightTrace t :=
            StepBoundary.eval_eq_rightTrace_of_between upper hts hs.2
              (fun r hr hrt => hqright r (hsubU hr) hrt)
          have hleftL : lower.leftTrace s = lower.rightTrace t := by
            rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem lower hnotL,
              StepBoundary.rightTrace_eq_eval, hevalL]
          have hleftU : upper.leftTrace s = upper.rightTrace t := by
            rw [StepBoundary.leftTrace_eq_rightTrace_of_not_mem upper hnotU,
              StepBoundary.rightTrace_eq_eval, hevalU]
          apply (mem_selValues_iff x).2
          exact ⟨by rw [hleftL]; exact hfour.2.1,
            by rw [StepBoundary.rightTrace_eq_eval, hevalL]; exact hfour.2.1,
            by rw [hleftU]; exact hfour.2.2.2,
            by rw [StepBoundary.rightTrace_eq_eval, hevalU]; exact hfour.2.2.2⟩

private lemma selValues_eval_subset {upper lower : StepBoundary} {t : unitInterval} {x : ℝ}
    (hx : x ∈ selValues upper lower t) :
    lower.eval t < (x : EReal) ∧ (x : EReal) < upper.eval t := by
  have hf := (mem_selValues_iff x).mp hx
  exact ⟨by simpa [StepBoundary.rightTrace] using hf.2.1,
    by simpa [StepBoundary.rightTrace] using hf.2.2.2⟩

private theorem hcont_admissible {upper lower : StepBoundary}
    (hstart : StartAdmissible upper lower) (hsep : TraceSeparated upper lower) :
    HasContinuousAdmissiblePath upper lower := by
  obtain ⟨g, hg, hgsel⟩ := selValues_openLowerSections.exists_continuous_selection
      (selValues_nonempty hsep) (selValues_convex upper lower)
  let knots := lower.knots ∪ upper.knots
  obtain ⟨q, hq, hqgap⟩ := StepBoundary.exists_right_gap_finset knots
      (show (⊥ : unitInterval) < ⊤ by norm_num)
  obtain ⟨δ, hδleft, hδright⟩ := exists_between (show (⊥ : unitInterval) < q by exact hq)
  have hsubL : lower.knots ⊆ knots := by
    intro r hr; exact Finset.mem_union.mpr (Or.inl hr)
  have hsubU : upper.knots ⊆ knots := by
    intro r hr; exact Finset.mem_union.mpr (Or.inr hr)
  have hevalL (t : unitInterval) (ht : t ≤ δ) : lower.eval t = lower.eval ⊥ := by
    by_cases htbot : t = ⊥
    · simp [htbot]
    · have hpos : ⊥ < t := bot_lt_iff_ne_bot.mpr htbot
      rw [← StepBoundary.rightTrace_eq_eval lower ⊥]
      exact StepBoundary.eval_eq_rightTrace_of_between lower hpos (lt_of_le_of_lt ht hδright)
        (fun r hr hrpos => hqgap r (hsubL hr) hrpos)
  have hevalU (t : unitInterval) (ht : t ≤ δ) : upper.eval t = upper.eval ⊥ := by
    by_cases htbot : t = ⊥
    · simp [htbot]
    · have hpos : ⊥ < t := bot_lt_iff_ne_bot.mpr htbot
      rw [← StepBoundary.rightTrace_eq_eval upper ⊥]
      exact StepBoundary.eval_eq_rightTrace_of_between upper hpos (lt_of_le_of_lt ht hδright)
        (fun r hr hrpos => hqgap r (hsubU hr) hrpos)
  let lam : unitInterval → ℝ := fun t => min ((t : ℝ) / (δ : ℝ)) 1
  have hδpos : 0 < (δ : ℝ) := by exact_mod_cast hδleft
  have hlamcont : Continuous lam := by
    dsimp [lam]
    fun_prop
  let f : C(unitInterval, ℝ) := ⟨fun t => lam t * g t, hlamcont.mul hg⟩
  have hf0 : f ⊥ = 0 := by
    change lam ⊥ * g ⊥ = 0
    simp [lam]
  refine ⟨f, hf0, ?_⟩
  constructor
  · simpa only [Skorokhod.ofContinuousMap_apply] using hf0
  · intro t
    simp only [Skorokhod.ofContinuousMap_apply]
    change lower.eval t < ((lam t * g t : ℝ) : EReal) ∧
      ((lam t * g t : ℝ) : EReal) < upper.eval t
    by_cases htδ : (t : ℝ) ≤ (δ : ℝ)
    · have htδ' : t ≤ δ := by exact_mod_cast htδ
      have hcoeff_nonneg : 0 ≤ lam t := by
        dsimp [lam]
        exact le_min (div_nonneg t.2.1 (le_of_lt hδpos)) zero_le_one
      have hcoeff_le : lam t ≤ 1 := by dsimp [lam]; exact min_le_right _ _
      have hcoeff2_nonneg : 0 ≤ 1 - lam t := sub_nonneg.mpr hcoeff_le
      have hcoeffsum : lam t + (1 - lam t) = 1 := by ring
      have hgInterval : lower.eval ⊥ < (g t : EReal) ∧ (g t : EReal) < upper.eval ⊥ := by
        have hgt := selValues_eval_subset (hgsel t)
        rw [hevalL t htδ', hevalU t htδ'] at hgt
        exact hgt
      have hzeroInterval : lower.eval ⊥ < (0 : EReal) ∧ (0 : EReal) < upper.eval ⊥ := hstart
      have hconv := convex_ereal_interval (lower.eval ⊥) (upper.eval ⊥)
        hgInterval hzeroInterval hcoeff_nonneg hcoeff2_nonneg hcoeffsum
      change lower.eval ⊥ <
          ((lam t • g t + (1 - lam t) • (0 : ℝ) : ℝ) : EReal) ∧
        ((lam t • g t + (1 - lam t) • (0 : ℝ) : ℝ) : EReal) < upper.eval ⊥ at hconv
      have heq : lam t • g t + (1 - lam t) • (0 : ℝ) = lam t * g t := by
        simp [smul_eq_mul]
      rw [hevalL t htδ', hevalU t htδ']
      rw [← heq]
      exact hconv
    · have hδt : δ < t := lt_of_not_ge (by exact_mod_cast htδ)
      have hratio : 1 ≤ (t : ℝ) / (δ : ℝ) :=
        (le_div_iff₀ hδpos).2 (by
          have hδt' : (δ : ℝ) ≤ (t : ℝ) := by exact_mod_cast hδt.le
          simpa using hδt')
      have hlamone : lam t = 1 := by simp [lam, hratio]
      have hgt := selValues_eval_subset (hgsel t)
      simpa [lam, hlamone] using hgt

/-- A corridor contains a continuous path starting at zero exactly when zero
is admissible at time zero and the left/right boundary traces have a strict
overlap at every time. The converse uses Mathlib's Michael selection theorem
on the trace-overlap intervals, then linearly pins the selected path to zero
before the first knot. -/
theorem hasContinuousAdmissiblePath_iff_startAndTraceSeparated
    {upper lower : StepBoundary} :
    HasContinuousAdmissiblePath upper lower ↔
      StartAdmissible upper lower ∧ TraceSeparated upper lower := by
  constructor
  · exact hasContinuousAdmissiblePath_implies_startAndTraceSeparated
  · rintro ⟨hstart, hsep⟩
    exact hcont_admissible hstart hsep

end ProbabilityTheory.RandomWalk.SmallDeviation
