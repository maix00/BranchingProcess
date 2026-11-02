/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Selection.NSelection.AtRank
public import Mathlib.Probability.Process.Stopping

/-!
# Ranked finite selection at a stopping time

## Public declarations

- `Combinatorics.Selection.NSelection.particleAtRankByAtStoppingTime`:
  selects a particle at rank `k` at finite stopping time `τ ω`, and returns
  `none` when `τ ω = ⊤`.
- `Combinatorics.Selection.NSelection.particleAtRankByAtStoppingTime_eq_finite`:
  if `τ ω = n`, the selector equals
  `particleAtRankBy (value n ω) (candidates n ω) k`.
- `Combinatorics.Selection.NSelection.particleRankVectorAtStoppingTime`:
  forms the vector of the first `m` ranks, using `default` for absent entries
  or an infinite stopping time.
- `Combinatorics.Selection.NSelection.measurable_particleRankVectorAtStoppingTime`:
  adapted finite-stage data makes this vector measurable with respect to the
  stopping-time σ-algebra.
- `Combinatorics.Selection.NSelection.particleRankVectorAtStoppingTime_mem`:
  when `τ ω = n` and `m ≤ (candidates n ω).card`, each vector entry is in
  `candidates n ω`.
- `Combinatorics.Selection.NSelection.particleRankVectorAtStoppingTime_rank`:
  under the same hypotheses, coordinate `i` has dynamic rank `i`.
- `Combinatorics.Selection.NSelection.particleRankVectorAtStoppingTime_rank_of_ne_default`:
  a coordinate different from `default` has its prescribed rank.
- `Combinatorics.Selection.NSelection.particleRankVectorAtStoppingTime_mem_of_ne_default`:
  a coordinate different from `default` belongs to the finite candidate set
  at the stopping generation.
- `Combinatorics.Selection.NSelection.particleRankVectorAtStoppingTime_injective`:
  under the finite-cardinality bound, the rank vector is injective.

For a stopping time \(\tau:\Omega\to\mathbb N\cup\{\infty\}\), the coordinate selector is
\[
  p_i(\omega)=
  \begin{cases}
    \operatorname{particleAtRankBy}(v_n(\omega),A_n(\omega),i),
      & \tau(\omega)=n,\\
    \mathrm{none}, & \tau(\omega)=\infty.
  \end{cases}
\]
The finite vector replaces an absent coordinate by the chosen default.

This module adds a finite order-statistic selector to Mathlib's general
stopping-time API. It is parameterized by arbitrary candidate and value types;
the filtration and stopping time are its only measure-theoretic data.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Selection.NSelection

/-- The particle of prescribed dynamic rank at a random stopping generation.
At `⊤` this is totalized to `none`; at a finite time it is the ordinary
finite-stage rank selector. -/
noncomputable def particleAtRankByAtStoppingTime
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (rank : ℕ) : Ω → Option ι :=
  fun ω => match τ ω with
  | ⊤ => none
  | (n : ℕ) => particleAtRankBy (value n ω) (candidates n ω) rank

@[simp] theorem particleAtRankByAtStoppingTime_eq_finite
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (rank : ℕ)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ)) :
    particleAtRankByAtStoppingTime τ value candidates rank ω =
      particleAtRankBy (value n ω) (candidates n ω) rank := by
  simp [particleAtRankByAtStoppingTime, hτ]

/-- A finite vector of the first `m` dynamic ranks at a stopping generation.
The default value only totalizes the selector when the stopping time is
infinite or the requested rank is absent. -/
noncomputable def particleRankVectorAtStoppingTime
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι) :
    Ω → Fin m → ι :=
  fun ω i => (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default

theorem measurable_particleRankVectorAtStoppingTime
    {Ω ι Value : Type*} [MeasurableSpace Ω] [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [LinearOrder ι] [LinearOrder Value]
    (F : Filtration ℕ inferInstance) (τ : Ω → WithTop ℕ)
    (hτ : IsStoppingTime F τ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι)
    (hcandidateFiber : ∀ n s, MeasurableSet[F n]
      {ω | candidates n ω = s})
    (hcandidateRange : ∀ n, (Set.range (candidates n)).Countable)
    (hkey : ∀ n p q, Measurable[F n]
      (fun ω => valueKey (value n ω) q < valueKey (value n ω) p))
    (m : ℕ) (default : ι) :
    Measurable[hτ.measurableSpace]
      (particleRankVectorAtStoppingTime τ value candidates m default) := by
  classical
  have hcoord : ∀ i : Fin m, Measurable[hτ.measurableSpace]
      (fun ω => particleRankVectorAtStoppingTime τ value candidates m default ω i) := by
    intro i
    have htime (n : ℕ) : MeasurableSet[hτ.measurableSpace]
        {ω | τ ω = (n : WithTop ℕ)} := hτ.measurableSet_eq_of_countable' n
    have timeCell (n : ℕ) (E : Set Ω) (hE : MeasurableSet[F n] E) :
        MeasurableSet[hτ.measurableSpace]
          (E ∩ {ω | τ ω = (n : WithTop ℕ)}) :=
      (hτ.measurableSet_inter_eq_iff E n).2
        (hE.inter (hτ.measurableSet_eq n))
    have htop : MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} :=
      hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ))
    have hsome (p : ι) (n : ℕ) : MeasurableSet[F n]
        {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = some p} := by
      letI : MeasurableSpace Ω := F n
      exact measurableSet_particleAtRankBy_eq_some (fun ω => value n ω)
        (fun ω => candidates n ω) (hcandidateFiber n) (hcandidateRange n)
        (hkey n) i.1 p
    have hnone (n : ℕ) : MeasurableSet[F n]
        {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = none} := by
      letI : MeasurableSpace Ω := F n
      exact measurableSet_particleAtRankBy_eq_none (fun ω => value n ω)
        (fun ω => candidates n ω) (hcandidateFiber n) (hcandidateRange n) i.1
    have hfiber (p : ι) : MeasurableSet[hτ.measurableSpace]
        {ω | (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default = p} := by
      by_cases hp : p = default
      · have hdecomp :
            {ω | (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default = p} =
              {ω | τ ω = ⊤} ∪ ⋃ n : ℕ,
                ({ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = none} ∪
                  {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = some p}) ∩
                    {ω | τ ω = (n : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion,
            Set.mem_inter_iff]
          cases ht : τ ω with
          | top => simp [particleAtRankByAtStoppingTime, ht, hp]
          | coe n =>
              rw [particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n ht]
              simp only [WithTop.coe_ne_top, false_or]
              cases hv : particleAtRankBy (value n ω) (candidates n ω) i.1 with
              | none =>
                  simp only [Option.getD_none]
                  constructor
                  · intro _
                    exact ⟨n, Or.inl hv, rfl⟩
                  · intro _
                    simp [hp]
              | some q =>
                  simp only [Option.getD_some]
                  constructor
                  · intro hqp
                    exact ⟨n, Or.inr (by simp [hv, hqp]), rfl⟩
                  · rintro ⟨k, hk, htime⟩
                    have hkn : k = n := (WithTop.coe_injective htime).symm
                    subst k
                    simp [hv] at hk
                    exact hk
        rw [hdecomp]
        refine htop.union (MeasurableSet.iUnion fun n => ?_)
        have hstage := (hnone n).union (hsome p n)
        exact timeCell n _ hstage
      · have hdecomp :
            {ω | (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default = p} =
              ⋃ n : ℕ,
                {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = some p} ∩
                  {ω | τ ω = (n : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
          cases ht : τ ω with
          | top =>
              have hdefaultNe : default ≠ p := fun h => hp h.symm
              simp [particleAtRankByAtStoppingTime, ht, hdefaultNe]
          | coe n =>
              rw [particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n ht]
              cases hv : particleAtRankBy (value n ω) (candidates n ω) i.1 with
              | none =>
                  simp only [Option.getD_none]
                  constructor
                  · intro hdefault
                    exact False.elim (hp (hdefault.symm))
                  · rintro ⟨k, hk, htime⟩
                    have hkn : k = n := (WithTop.coe_injective htime).symm
                    subst k
                    exact False.elim (by simp [hv] at hk)
              | some q =>
                  simp only [Option.getD_some]
                  constructor
                  · intro hqp
                    exact ⟨n, by simp [hv, hqp], rfl⟩
                  · rintro ⟨k, hk, htime⟩
                    have hkn : k = n := (WithTop.coe_injective htime).symm
                    subst k
                    simp [hv] at hk
                    exact hk
        rw [hdecomp]
        exact MeasurableSet.iUnion fun n => timeCell n _ (hsome p n)
    letI : MeasurableSpace Ω := hτ.measurableSpace
    change Measurable (fun ω => particleRankVectorAtStoppingTime
      τ value candidates m default ω i)
    apply measurable_to_countable'
    intro p
    have hset :
        (fun ω => particleRankVectorAtStoppingTime τ value candidates m default ω i) ⁻¹'
          {p} =
        {ω | particleRankVectorAtStoppingTime τ value candidates m default ω i = p} := by
      ext ω
      simp
    rw [hset]
    exact hfiber p
  letI : MeasurableSpace Ω := hτ.measurableSpace
  exact measurable_pi_iff.mpr hcoord


/-- At a finite stopping generation, every requested rank below the candidate
cardinality is realized in the candidate set. -/
theorem particleRankVectorAtStoppingTime_mem
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (hm : m ≤ (candidates n ω).card) (i : Fin m) :
    particleRankVectorAtStoppingTime τ value candidates m default ω i ∈
      candidates n ω := by
  classical
  have hi : i.1 < (candidates n ω).card := lt_of_lt_of_le i.2 hm
  have hsome : particleAtRankBy (value n ω) (candidates n ω) i.1 ≠ none := by
    intro hnone
    have hcard := (particleAtRankBy_eq_none_iff).mp hnone
    omega
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' := (particleAtRankBy_eq_some_iff).mp hp.symm
  simpa [particleRankVectorAtStoppingTime,
    particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n hτ,
    hp.symm] using hp'.1

/-- The stopped rank vector has the prescribed ranks; consequently its
coordinates are pairwise distinct whenever it is requested below the finite
candidate cardinality. -/
theorem particleRankVectorAtStoppingTime_rank
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (hm : m ≤ (candidates n ω).card) (i : Fin m) :
    rankBy (value n ω) (candidates n ω)
      (particleRankVectorAtStoppingTime τ value candidates m default ω i) = i.1 := by
  classical
  have hmem := particleRankVectorAtStoppingTime_mem τ value candidates m default
    ω n hτ hm i
  have hi : i.1 < (candidates n ω).card := lt_of_lt_of_le i.2 hm
  have hsome : particleAtRankBy (value n ω) (candidates n ω) i.1 ≠ none := by
    intro hnone
    have hcard := (particleAtRankBy_eq_none_iff).mp hnone
    omega
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' := (particleAtRankBy_eq_some_iff).mp hp.symm
  have hpvec : particleRankVectorAtStoppingTime τ value candidates m default ω i = p := by
    simp [particleRankVectorAtStoppingTime,
      particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n hτ, hp.symm]
  rw [hpvec]
  exact hp'.2

/-- If a stopped rank selector is not its default sentinel, it is the genuine
particle at that rank, without a separate lower bound on the whole finite
population. -/
theorem particleRankVectorAtStoppingTime_rank_of_ne_default
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (i : Fin m)
    (hne : particleRankVectorAtStoppingTime τ value candidates m default ω i ≠ default) :
    rankBy (value n ω) (candidates n ω)
      (particleRankVectorAtStoppingTime τ value candidates m default ω i) = i.1 := by
  classical
  have hsome : particleAtRankByAtStoppingTime τ value candidates i.1 ω ≠ none := by
    intro hnone
    apply hne
    simp [particleRankVectorAtStoppingTime, hnone]
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' : particleAtRankBy (value n ω) (candidates n ω) i.1 = some p := by
    simpa [particleAtRankByAtStoppingTime, hτ] using hp.symm
  have hvec : particleRankVectorAtStoppingTime τ value candidates m default ω i = p := by
    simp [particleRankVectorAtStoppingTime, hp.symm]
  rw [hvec]
  exact (particleAtRankBy_eq_some_iff.mp hp').2

/-- A nondefault stopped rank is an actual member of the candidate population,
even when the requested rank is not known to exist uniformly on every raw
field. -/
theorem particleRankVectorAtStoppingTime_mem_of_ne_default
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (i : Fin m)
    (hne : particleRankVectorAtStoppingTime τ value candidates m default ω i ≠ default) :
    particleRankVectorAtStoppingTime τ value candidates m default ω i ∈ candidates n ω := by
  classical
  have hsome : particleAtRankByAtStoppingTime τ value candidates i.1 ω ≠ none := by
    intro hnone
    apply hne
    simp [particleRankVectorAtStoppingTime, hnone]
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' : particleAtRankBy (value n ω) (candidates n ω) i.1 = some p := by
    simpa [particleAtRankByAtStoppingTime, hτ] using hp.symm
  have hvec : particleRankVectorAtStoppingTime τ value candidates m default ω i = p := by
    simp [particleRankVectorAtStoppingTime, hp.symm]
  rw [hvec]
  exact (particleAtRankBy_eq_some_iff.mp hp').1

/-- Distinctness of the enumerated stopped population follows from the
injectivity of dynamic rank on a finite candidate set. -/
theorem particleRankVectorAtStoppingTime_injective
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (hm : m ≤ (candidates n ω).card) :
    Function.Injective (particleRankVectorAtStoppingTime τ value candidates m default ω) := by
  intro i j hij
  apply Fin.ext
  have hi := particleRankVectorAtStoppingTime_rank τ value candidates m default ω n hτ hm i
  have hj := particleRankVectorAtStoppingTime_rank τ value candidates m default ω n hτ hm j
  rw [hij] at hi
  omega


end Combinatorics.Selection.NSelection
