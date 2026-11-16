/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Splits
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Population.RootIndexed
import Combinatorics.UlamHarris.Order

/-!
# Descendant roots of the first successful growth trial

## Public declarations

* `exists_firstSuccessfulTrialRoots`: at the first successful completion
  $\tau$, choose $m$ distinct members of that trial's terminal population.
  The vector is $\mathcal F_\tau$-measurable and its members have depth $\tau$.
  At $\tau=k+1+d$ all chosen roots belong to the age-$d$ descendants of the
  growth child of the split at generation $k$.

This is the stopped root vector used to restart the process in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.2.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion

open Combinatorics.Branching Combinatorics.UlamHarris
open GrowthTrial GrowthTrial.Population

/-- A stopped-measurable enumeration of a prescribed number of terminal
particles of the successful trial. -/
public theorem exists_firstSuccessfulTrialRoots
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (m lower upper duration : ℕ) (hm : m ≤ lower) (hupper : 1 ≤ upper) (r : ℕ) :
    let Ω := RootIndexed.StepField ℕ ℕ ℝ
    let τ := firstSuccessfulCompletion R growth hR lower upper duration r
    let hτ := firstSuccessfulCompletion_isStoppingTime R growth hR hgrowth lower upper duration r
    ∃ roots : Ω → Fin m → RootIndexed.TreeNode ℕ ℕ,
      (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) ∧
      (∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) → ∀ i, (roots ω i).2.length = n) ∧
      (∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) ∧
      ∀ ω k, τ ω = ((k + 1 + duration : ℕ) : WithTop ℕ) →
        ∀ i, roots ω i ∈ capStoppedCandidate (lineages R hR) R growth upper r
          PUnit.unit (k + 1) duration ω := by
  classical
  intro Ω τ hτ
  let F := RootIndexed.stepFiltration (Root := ℕ) (α := ℕ) (X := ℝ)
  let Node := RootIndexed.TreeNode ℕ ℕ
  let chooseFrom (s : Finset Node) (i : Fin m) : Node :=
    if hs : m ≤ s.card then (Function.Embedding.exists_of_card_le_finset
      (α := Fin m) (s := s) (by simpa using hs)).choose i else (r, [])
  have hchoose (s : Finset Node) (hs : m ≤ s.card) :
      (∀ i, chooseFrom s i ∈ s) ∧ Function.Injective (chooseFrom s) := by
    let h := Function.Embedding.exists_of_card_le_finset
      (α := Fin m) (s := s) (by simpa using hs)
    refine ⟨fun i => ?_, ?_⟩
    · rw [show chooseFrom s i = h.choose i by simp only [chooseFrom, dite_eq_left hs]]
      exact h.choose_spec (Set.mem_range_self i)
    · simpa only [chooseFrom, dite_eq_left hs] using h.choose.injective
  let population (n : ℕ) (ω : Ω) : Finset Node :=
    if duration ≤ n then capStoppedCandidate (lineages R hR) R growth upper r
      PUnit.unit (n - duration) duration ω else ∅
  have hpop (n : ℕ) : Measurable[F n] (population n) := by
    by_cases hn : duration ≤ n
    · have hm := capStoppedCandidate_adapted (lineages R hR) R growth hR hgrowth upper r
        PUnit.unit (n - duration) duration
      rw [Nat.sub_add_cancel hn] at hm
      simpa only [population, ite_eq_left hn] using hm
    · simpa only [population, ite_eq_right hn] using
        (measurable_const (a := (∅ : Finset Node)) :
          Measurable[F n] (fun _ : Ω => (∅ : Finset Node)))
  let roots (ω : Ω) : Fin m → Node :=
    match τ ω with
    | ⊤ => fun _ => (r, [])
    | (n : ℕ) => chooseFrom (population n ω)
  have hrootAt (ω : Ω) (n : ℕ) (ht : τ ω = (n : WithTop ℕ)) :
      roots ω = chooseFrom (population n ω) := by simp [roots, ht]
  have htrial (ω : Ω) (n : ℕ) (ht : τ ω = (n : WithTop ℕ)) :
      ∃ k, n = k + 1 + duration ∧ m ≤ (population n ω).card := by
    let declarations : ℕ → Set Ω := fun t => {ω | ∃ k,
      ((k + 1 + duration : ℕ) : WithTop ℕ) = t ∧
        ω ∈ successEvent R growth hR lower upper duration r k}
    have hfirst : firstDeclaredSuccess declarations ω = (n : WithTop ℕ) := ht
    obtain ⟨k, hk, hs⟩ := ((firstDeclaredSuccess_eq_iff declarations ω n).mp hfirst).1
    have hn : k + 1 + duration = n := WithTop.coe_injective hk
    refine ⟨k, hn.symm, ?_⟩
    subst n
    have hcard := rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess
      growth lower upper duration ω
      (growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) ω)
      hupper hs.2.2
    simpa [population, capStoppedCandidate] using hm.trans hcard
  refine ⟨roots, ?_, ?_, ?_, ?_⟩
  · intro v
    have hset : {ω | roots ω = v} =
        ⋃ t : WithTop ℕ, {ω | roots ω = v} ∩ {ω | τ ω = t} := by
      ext ω
      simp [and_comm]
    rw [hset]
    apply MeasurableSet.iUnion
    intro t
    cases t with
    | top =>
      have heq : {ω | roots ω = v} ∩ {ω | τ ω = ⊤} =
          {ω : Ω | (fun _ : Fin m => ((r, []) : Node)) = v} ∩ {ω | τ ω = ⊤} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        apply and_congr_left
        intro ht
        simp [roots, ht]
      rw [heq]
      exact (measurable_const (measurableSet_singleton _)).inter
        (hτ.measurable (measurableSet_singleton _))
    | coe n =>
      have heq : {ω | roots ω = v} ∩ {ω | τ ω = (n : WithTop ℕ)} =
          {ω | chooseFrom (population n ω) = v} ∩ {ω | τ ω = (n : WithTop ℕ)} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact and_congr_left fun ht => by rw [hrootAt ω n ht]
      change MeasurableSet[hτ.measurableSpace] ({ω | roots ω = v} ∩ {ω | τ ω = (n : WithTop ℕ)})
      rw [heq]
      apply (hτ.measurableSet_inter_eq_iff _ n).2
      exact (((measurable_of_countable chooseFrom).comp (hpop n))
        (measurableSet_singleton _)).inter (hτ.measurableSet_eq n)
  · intro ω n ht i
    obtain ⟨k, hk, hc⟩ := htrial ω n ht
    have hm := (hchoose (population n ω) hc).1 i
    rw [hrootAt ω n ht]
    have hpopEq : population n ω =
        capStoppedCandidate (lineages R hR) R growth upper r PUnit.unit (n - duration) duration ω := by
      simp only [population, ite_eq_left (show duration ≤ n by omega)]
    have hm' : chooseFrom (population n ω) i ∈
        capStoppedCandidate (lineages R hR) R growth upper r PUnit.unit (n - duration) duration ω :=
      hpopEq ▸ hm
    have hd := rootedCapStoppedPopulation_node_depth growth upper ω _ _ duration hm'
    rw [growthTrialRootAt_depth] at hd
    exact hd.trans (Nat.sub_add_cancel (by omega))
  · intro ω hfinite
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
    rw [hrootAt ω n hn.symm]
    obtain ⟨_, _, hcard⟩ := htrial ω n hn.symm
    exact (hchoose (population n ω) hcard).2
  · intro ω k ht i
    rw [hrootAt ω (k + 1 + duration) ht]
    obtain ⟨_, _, hc⟩ := htrial ω (k + 1 + duration) ht
    simpa [population] using (hchoose (population (k + 1 + duration) ω) hc).1 i

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion
