/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Representation.Continuous
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Data.NNRat.Encodable
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.LinearGrowth
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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
- `ProbabilityTheory.hasApproxWindowBefore_of_nonnegativeWindowStart`:
  a qualifying start $t\le u$ gives a rational-start finite-grid
  approximation at every grid size.
- `ProbabilityTheory.hasApproxFirstWindowBefore_of_firstWindow_le`:
  $T^s(f)\le u$ implies the countable rational-grid condition.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_le_iff_hasApproxFirstWindowBefore`:
  for $u+1\le s$, the event $\{T^s\le u\}$ equals the rational-grid
  event in the proof of Bolthausen's Lemma 2.1.
- `ProbabilityTheory.measurable_firstNonnegativeWindowStartUpTo`:
  $f\mapsto T^s(f)$ is Borel measurable for every finite horizon $s$.
- `ProbabilityTheory.firstNonnegativeWindowStart_eq_iInf_upTo`:
  $T(f)=\inf_{n\in\mathbb N}T^n(f)$.
- `ProbabilityTheory.measurable_firstNonnegativeWindowStart`:
  $f\mapsto T(f)=T^\infty(f)$ is Borel measurable.
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
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_eq_first_of_ne_top`:
  $T^s(f)<\infty$ implies $T^s(f)=T(f)$.

These are deterministic ingredients of the first-window time $T^s$ in
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Section 2, definition (2.1),
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

private theorem exists_nonnegativeRational_near
    (t : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℚ≥0, dist (r : ℝ≥0) t < δ := by
  have hleft : max (0 : ℝ) ((t : ℝ) - δ) < (t : ℝ) + δ := by
    apply max_lt
    · exact add_pos_of_nonneg_of_pos t.property hδ
    · linarith
  obtain ⟨q, hqleft, hqright⟩ := exists_rat_btwn hleft
  have hq0 : (0 : ℚ) ≤ q := by
    exact_mod_cast (le_trans (le_max_left _ _) hqleft.le)
  let r : ℚ≥0 := ⟨q, hq0⟩
  refine ⟨r, ?_⟩
  rw [NNReal.dist_eq]
  have hcast : ((r : ℝ≥0) : ℝ) = (r : ℝ) := by
    norm_cast
  rw [hcast]
  have hlow : (t : ℝ) - δ < (r : ℝ) := by
    exact (le_max_right (0 : ℝ) _).trans_lt hqleft
  have hupp : (r : ℝ) < (t : ℝ) + δ := hqright
  rw [abs_lt]
  constructor <;> linarith

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

/-- A true qualifying window yields the rational finite-grid inequality
at every fixed grid size, as in the forward implication of Bolthausen's
Lemma 2.1. Continuity permits a nearby rational starting time. -/
theorem hasApproxWindowBefore_of_nonnegativeWindowStart
    (f : C(ℝ≥0, ℝ)) (n : ℕ) {t u : ℝ≥0}
    (ht : IsNonnegativeWindowStart f t) (htu : t ≤ u) :
    HasApproxWindowBefore n u f := by
  let grid (i : Fin n) : ℝ≥0 :=
    ((i : ℝ≥0) + 1) / (n + 1)
  let ε : ℝ := 1 / (n + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hgrid (i : Fin n) : grid i ≤ 1 := by
    dsimp [grid]
    apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < n + 1)).2
    have hi : (i : ℕ) + 1 ≤ n + 1 := Nat.succ_le_succ i.isLt.le
    simpa only [one_mul] using
      (show (i : ℝ≥0) + 1 ≤ (n : ℝ≥0) + 1 by exact_mod_cast hi)
  have htgrid (i : Fin n) : f t < f (t + grid i) + ε := by
    exact lt_add_of_le_of_pos (ht ⟨grid i, ⟨bot_le, hgrid i⟩⟩) hε
  let A : Set ℝ≥0 :=
    {r | ∀ i : Fin n, f r < f (r + grid i) + ε} ∩
      {r | r < u + 1 / (n + 1)}
  have hAopen : IsOpen A := by
    apply IsOpen.inter
    · have hopen : IsOpen (⋂ i : Fin n,
          {r : ℝ≥0 | f r < f (r + grid i) + ε}) := by
        apply isOpen_iInter_of_finite
        intro i
        exact isOpen_lt f.continuous
          ((f.continuous.comp (continuous_id.add continuous_const)).add
            continuous_const)
      simpa only [Set.iInter_ofPred] using hopen
    · exact isOpen_Iio
  have hAstart : t ∈ A := by
    constructor
    · exact htgrid
    · have hpositive : (0 : ℝ≥0) < 1 / (n + 1) := by positivity
      exact htu.trans_lt (lt_add_of_pos_right u hpositive)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hAopen.mem_nhds hAstart)
  obtain ⟨r, hr⟩ := exists_nonnegativeRational_near t hδ
  have hrA : (r : ℝ≥0) ∈ A := hball hr
  refine ⟨r, hrA.2.le, ?_⟩
  intro i
  exact (hrA.1 i).le

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

private theorem exists_convergent_approxWindowStarts
    (f : C(ℝ≥0, ℝ)) (u : ℝ≥0)
    (happrox : HasApproxFirstWindowBefore u f) :
    ∃ r : ℕ → ℚ≥0,
      (∀ n, (r n : ℝ≥0) ≤ u + 1 / (n + 1) ∧
        ApproxNonnegativeWindowStart n (r n : ℝ≥0) f) ∧
      ∃ t : ℝ≥0, t ≤ u ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Filter.Tendsto (fun n => (r (φ n) : ℝ≥0))
            Filter.atTop (𝓝 t) := by
  classical
  let r (n : ℕ) : ℚ≥0 := Classical.choose (happrox n)
  have hr (n : ℕ) :
      (r n : ℝ≥0) ≤ u + 1 / (n + 1) ∧
        ApproxNonnegativeWindowStart n (r n : ℝ≥0) f :=
    Classical.choose_spec (happrox n)
  have hbound (n : ℕ) : (r n : ℝ≥0) ∈ Set.Icc 0 (u + 1) := by
    constructor
    · exact bot_le
    · have hone : (1 : ℝ≥0) / (n + 1) ≤ 1 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < n + 1)).2
        have hn : (1 : ℝ≥0) ≤ n + 1 := by
          exact_mod_cast (Nat.le_add_left 1 n)
        simpa only [one_mul] using hn
      have hplus : u + (1 : ℝ≥0) / (n + 1) ≤ u + 1 :=
        add_le_add_right hone u
      exact (hr n).1.trans hplus
  obtain ⟨t, _, φ, hφ, hconv⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) (u + 1))).tendsto_subseq
      (x := fun n => (r n : ℝ≥0)) hbound
  have hφtop : Filter.Tendsto φ Filter.atTop Filter.atTop :=
    hφ.tendsto_atTop
  have hrecip : Filter.Tendsto
      (fun n => (1 : ℝ≥0) / ((φ n : ℝ≥0) + 1))
      Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφtop
  have hupper : Filter.Tendsto
      (fun n => u + (1 : ℝ≥0) / ((φ n : ℝ≥0) + 1))
      Filter.atTop (𝓝 u) := by
    simpa using Filter.Tendsto.add tendsto_const_nhds hrecip
  have htu : t ≤ u :=
    le_of_tendsto_of_tendsto hconv hupper
      (Filter.Eventually.of_forall fun n => (hr (φ n)).1)
  exact ⟨r, hr, t, htu, φ, hφ, hconv⟩

private theorem eventually_exists_finiteGridPoint_between
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ i : Fin n,
      a ≤ (((((i : ℝ≥0) + 1) / (n + 1) : ℝ≥0) : ℝ)) ∧
        (((((i : ℝ≥0) + 1) / (n + 1) : ℝ≥0) : ℝ)) ≤ b := by
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      ∃ j : ℕ, a * ((n : ℝ) + 1) ≤ j ∧
        (j : ℝ) ≤ b * ((n : ℝ) + 1) := by
    have htop : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hevent := LinearGrowth.Real.eventually_atTop_exists_nat_between
      hab (ha.le.trans hab.le)
    simpa only [Nat.cast_add, Nat.cast_one] using htop.eventually hevent
  filter_upwards [hlarge] with n ⟨j, hjlow, hjup⟩
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hjposReal : (0 : ℝ) < j :=
    (mul_pos ha hnpos).trans_le hjlow
  have hjpos : 0 < j := by exact_mod_cast hjposReal
  have hjltReal : (j : ℝ) < (n : ℝ) + 1 :=
    hjup.trans_lt (mul_lt_of_lt_one_left hnpos hb)
  have hjle : j ≤ n := by
    have : j < n + 1 := by exact_mod_cast hjltReal
    omega
  let i : Fin n := ⟨j - 1, by omega⟩
  have hgrid : ((i : ℝ≥0) + 1) = (j : ℝ≥0) := by
    exact_mod_cast Nat.sub_add_cancel hjpos
  refine ⟨i, ?_, ?_⟩
  · rw [hgrid, NNReal.coe_div]
    exact (le_div_iff₀ hnpos).2 hjlow
  · rw [hgrid, NNReal.coe_div]
    exact (div_le_iff₀ hnpos).2 hjup

private theorem exists_nonnegativeWindowStart_of_hasApproxFirstWindowBefore
    (f : C(ℝ≥0, ℝ)) (u : ℝ≥0)
    (happrox : HasApproxFirstWindowBefore u f) :
    ∃ t : ℝ≥0, t ≤ u ∧ IsNonnegativeWindowStart f t := by
  obtain ⟨r, hr, t, htu, φ, hφ, hconv⟩ :=
    exists_convergent_approxWindowStarts f u happrox
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hrecip : Tendsto (fun k : ℕ =>
      (1 : ℝ) / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφtop
  have hinterior (v : ℝ≥0) (hv0 : 0 < v) (hv1 : v < 1) :
      f t ≤ f (t + v) := by
    by_contra hle
    have hgap : f (t + v) < f t := lt_of_not_ge hle
    let ε : ℝ := (f t - f (t + v)) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    let O : Set (ℝ≥0 × ℝ≥0) :=
      {p | f (p.1 + p.2) + ε < f p.1}
    have hOopen : IsOpen O := by
      exact isOpen_lt
        ((f.continuous.comp (continuous_fst.add continuous_snd)).add
          continuous_const)
        (f.continuous.comp continuous_fst)
    have htO : (t, v) ∈ O := by
      dsimp [O, ε]
      linarith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
      (hOopen.mem_nhds htO)
    let a : ℝ := max ((v : ℝ) / 2) ((v : ℝ) - δ / 2)
    let b : ℝ := min (((v : ℝ) + 1) / 2) ((v : ℝ) + δ / 2)
    have hv0r : (0 : ℝ) < v := by exact_mod_cast hv0
    have hv1r : (v : ℝ) < 1 := by exact_mod_cast hv1
    have ha0 : 0 < a := by dsimp [a]; linarith [le_max_left ((v : ℝ) / 2) ((v : ℝ) - δ / 2)]
    have hav : a < (v : ℝ) := by
      dsimp [a]
      rw [max_lt_iff]
      constructor <;> linarith
    have hvb : (v : ℝ) < b := by
      dsimp [b]
      rw [lt_min_iff]
      constructor <;> linarith
    have hb1 : b < 1 := by
      dsimp [b]
      linarith [min_le_left (((v : ℝ) + 1) / 2) ((v : ℝ) + δ / 2)]
    have halow : (v : ℝ) - δ < a := by
      dsimp [a]
      linarith [le_max_right ((v : ℝ) / 2) ((v : ℝ) - δ / 2)]
    have hbup : b < (v : ℝ) + δ := by
      dsimp [b]
      linarith [min_le_right (((v : ℝ) + 1) / 2) ((v : ℝ) + δ / 2)]
    have hgrid : ∀ᶠ k : ℕ in atTop, ∃ i : Fin (φ k),
        a ≤ (((((i : ℝ≥0) + 1) / (φ k + 1) : ℝ≥0) : ℝ)) ∧
          (((((i : ℝ≥0) + 1) / (φ k + 1) : ℝ≥0) : ℝ)) ≤ b :=
      hφtop.eventually
        (eventually_exists_finiteGridPoint_between ha0 (hav.trans hvb) hb1)
    have hstart : ∀ᶠ k : ℕ in atTop,
        dist (r (φ k) : ℝ≥0) t < δ :=
      hconv.eventually (Metric.ball_mem_nhds _ hδ)
    have hsmall : ∀ᶠ k : ℕ in atTop,
        (1 : ℝ) / ((φ k : ℝ) + 1) < ε :=
      hrecip.eventually (Iio_mem_nhds hε)
    obtain ⟨k, ⟨i, hailow, hiup⟩, hkstart, hksmall⟩ :=
      (hgrid.and (hstart.and hsmall)).exists
    let w : ℝ≥0 := ((i : ℝ≥0) + 1) / (φ k + 1)
    have hwnear : dist w v < δ := by
      rw [NNReal.dist_eq, abs_lt]
      dsimp [w] at hailow hiup ⊢
      constructor <;> linarith
    have hpair : ((r (φ k) : ℝ≥0), w) ∈ O := by
      apply hball
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨hkstart, hwnear⟩
    have happroxGrid := (hr (φ k)).2 i
    have hOfact : f ((r (φ k) : ℝ≥0) + w) + ε <
        f (r (φ k) : ℝ≥0) := hpair
    dsimp [w] at hOfact
    linarith
  have hclosed : IsClosed {v : ℝ≥0 | f t ≤ f (t + v)} :=
    isClosed_le continuous_const
      (f.continuous.comp (continuous_const.add continuous_id))
  have hIoo : Set.Ioo (0 : ℝ≥0) 1 ⊆
      {v : ℝ≥0 | f t ≤ f (t + v)} := by
    intro v hv
    exact hinterior v hv.1 hv.2
  have hIcc : Set.Icc (0 : ℝ≥0) 1 ⊆
      {v : ℝ≥0 | f t ≤ f (t + v)} := by
    rw [← closure_Ioo (by norm_num : (0 : ℝ≥0) ≠ 1)]
    exact closure_minimal hIoo hclosed
  exact ⟨t, htu, fun v => hIcc v.property⟩

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

/-- The forward implication in the rational-grid description of
$\{T^s\le u\}$ from Bolthausen's Lemma 2.1. -/
theorem hasApproxFirstWindowBefore_of_firstWindow_le
    (f : C(ℝ≥0, ℝ)) (s u : ℝ≥0)
    (hfirst : firstNonnegativeWindowStartUpTo f s ≤ u) :
    HasApproxFirstWindowBefore u f := by
  have hfinite : firstNonnegativeWindowStartUpTo f s < ⊤ :=
    hfirst.trans_lt (WithTop.coe_lt_top u)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
    (WithTop.lt_top_iff_ne_top.mp hfinite)
  have heligible : IsNonnegativeWindowStart f t :=
    ((firstNonnegativeWindowStartUpTo_eq_coe_iff f s t).mp ht.symm).2.1
  have htu : t ≤ u := WithTop.coe_le_coe.mp (ht ▸ hfirst)
  intro n
  exact hasApproxWindowBefore_of_nonnegativeWindowStart f n heligible htu

/-- Bolthausen's rational-grid identity for the finite-horizon first
window, Lemma 2.1, p. 481. The horizon condition ensures that every
candidate start before $u$ has its full unit window inside $[0,s]$. -/
theorem firstNonnegativeWindowStartUpTo_le_iff_hasApproxFirstWindowBefore
    (f : C(ℝ≥0, ℝ)) (s u : ℝ≥0) (hus : u + 1 ≤ s) :
    firstNonnegativeWindowStartUpTo f s ≤ u ↔
      HasApproxFirstWindowBefore u f := by
  constructor
  · exact hasApproxFirstWindowBefore_of_firstWindow_le f s u
  · intro happrox
    obtain ⟨t, htu, ht⟩ :=
      exists_nonnegativeWindowStart_of_hasApproxFirstWindowBefore
        f u happrox
    have hts : t + 1 ≤ s := by
      exact (add_le_add_left htu 1).trans hus
    have hnonempty : ∃ r : ℝ≥0,
        r + 1 ≤ s ∧ IsNonnegativeWindowStart f r :=
      ⟨t, hts, ht⟩
    have hfirst : firstNonnegativeWindowStartUpTo f s ≤ t := by
      simp only [firstNonnegativeWindowStartUpTo, dite_eq_left hnonempty,
        WithTop.coe_le_coe]
      exact csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨hts, ht⟩
    exact hfirst.trans (WithTop.coe_le_coe.mpr htu)

/-- For every finite horizon, a lower level set of the first-window
time is a Borel path event. -/
theorem measurableSet_firstNonnegativeWindowStartUpTo_le
    (s u : ℝ≥0) :
    MeasurableSet {f : C(ℝ≥0, ℝ) |
      firstNonnegativeWindowStartUpTo f s ≤ u} := by
  by_cases hs : 1 ≤ s
  · let v : ℝ≥0 := min u (s - 1)
    have hv : v + 1 ≤ s := by
      have hsub : s - 1 + 1 = s := tsub_add_cancel_of_le hs
      exact (add_le_add_left (min_le_right u (s - 1)) 1).trans_eq hsub
    have hset : {f : C(ℝ≥0, ℝ) |
        firstNonnegativeWindowStartUpTo f s ≤ u} =
        {f | firstNonnegativeWindowStartUpTo f s ≤ v} := by
      ext f
      constructor
      · intro hfirst
        have hfinite : firstNonnegativeWindowStartUpTo f s < ⊤ :=
          hfirst.trans_lt (WithTop.coe_lt_top u)
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
          (WithTop.lt_top_iff_ne_top.mp hfinite)
        have hts : t + 1 ≤ s :=
          ((firstNonnegativeWindowStartUpTo_eq_coe_iff f s t).mp
            ht.symm).1
        have htu : t ≤ u := WithTop.coe_le_coe.mp (ht ▸ hfirst)
        have hthorizon : t ≤ s - 1 :=
          (le_tsub_iff_right hs).2 hts
        have htv : t ≤ v := le_min htu hthorizon
        change firstNonnegativeWindowStartUpTo f s ≤ (v : WithTop ℝ≥0)
        rw [← ht]
        exact WithTop.coe_le_coe.mpr htv
      · exact fun hfirst => hfirst.trans
          (WithTop.coe_le_coe.mpr (min_le_left u (s - 1)))
    rw [hset]
    have happrox : {f : C(ℝ≥0, ℝ) |
        firstNonnegativeWindowStartUpTo f s ≤ v} =
        {f | HasApproxFirstWindowBefore v f} := by
      ext f
      exact firstNonnegativeWindowStartUpTo_le_iff_hasApproxFirstWindowBefore
        f s v hv
    rw [happrox]
    exact measurableSet_hasApproxFirstWindowBefore v
  · have hslt : s < 1 := lt_of_not_ge hs
    have htop (f : C(ℝ≥0, ℝ)) :
        firstNonnegativeWindowStartUpTo f s = ⊤ := by
      have hnone : ¬ ∃ t : ℝ≥0,
          t + 1 ≤ s ∧ IsNonnegativeWindowStart f t := by
        rintro ⟨t, hts, _⟩
        have hle : (1 : ℝ≥0) ≤ t + 1 := by
          exact le_add_of_nonneg_left t.property
        exact (not_le_of_gt hslt) (hle.trans hts)
      simp [firstNonnegativeWindowStartUpTo, hnone]
    have hset : {f : C(ℝ≥0, ℝ) |
        firstNonnegativeWindowStartUpTo f s ≤ u} = ∅ := by
      ext f
      constructor
      · intro hf
        change firstNonnegativeWindowStartUpTo f s ≤
          (u : WithTop ℝ≥0) at hf
        rw [htop f] at hf
        exact (not_le_of_gt (WithTop.coe_lt_top u)) hf
      · intro hf
        simp at hf
    rw [hset]
    exact MeasurableSet.empty

/-- Bolthausen's Lemma 2.1: the first eligible window time is Borel
measurable on continuous path space for every finite horizon. -/
theorem measurable_firstNonnegativeWindowStartUpTo (s : ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) =>
      firstNonnegativeWindowStartUpTo f s) := by
  apply measurable_of_Iic
  intro x
  cases x with
  | top => simp
  | coe u =>
      simpa only [Set.preimage, Set.mem_Iic, Set.mem_ofPred_eq] using
        measurableSet_firstNonnegativeWindowStartUpTo_le s u

/-- The unrestricted first eligible window is the decreasing limit of
the finite-horizon first-window times. -/
theorem firstNonnegativeWindowStart_eq_iInf_upTo
    (f : C(ℝ≥0, ℝ)) :
    firstNonnegativeWindowStart f =
      ⨅ n : ℕ, firstNonnegativeWindowStartUpTo f n := by
  apply le_antisymm
  · exact le_iInf fun n => firstNonnegativeWindowStart_le_upTo f n
  · by_cases hfinite : ∃ t : ℝ≥0, IsNonnegativeWindowStart f t
    · obtain ⟨t, ht, hmin⟩ :=
        exists_earliestNonnegativeWindowStart f hfinite
      have hfirst : firstNonnegativeWindowStart f = t :=
        (firstNonnegativeWindowStart_eq_coe_iff f t).mpr
          ⟨ht, hmin⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (t + 1)
      have hcut : firstNonnegativeWindowStartUpTo f n = t :=
        firstNonnegativeWindowStartUpTo_eq_first_of_le f hfirst hn.le
      calc
        (⨅ m : ℕ, firstNonnegativeWindowStartUpTo f m) ≤
            firstNonnegativeWindowStartUpTo f n := iInf_le _ n
        _ = firstNonnegativeWindowStart f := by rw [hcut, hfirst]
    · have htop : firstNonnegativeWindowStart f = ⊤ := by
        simp [firstNonnegativeWindowStart, hfinite]
      rw [htop]
      exact le_top

/-- Bolthausen's Lemma 2.1 also covers $T=T^\infty$: the unrestricted
first-window time is Borel measurable as a countable infimum of the
finite-horizon times. -/
theorem measurable_firstNonnegativeWindowStart :
    Measurable (fun f : C(ℝ≥0, ℝ) =>
      firstNonnegativeWindowStart f) := by
  have hmeas : Measurable (fun f : C(ℝ≥0, ℝ) =>
      ⨅ n : ℕ, firstNonnegativeWindowStartUpTo f n) :=
    Measurable.iInf fun n => measurable_firstNonnegativeWindowStartUpTo n
  convert hmeas using 1
  funext f
  exact firstNonnegativeWindowStart_eq_iInf_upTo f

end ProbabilityTheory

end
