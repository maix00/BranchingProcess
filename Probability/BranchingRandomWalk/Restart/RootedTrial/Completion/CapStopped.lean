/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Restart.Trial.Basic
public import Probability.BranchingRandomWalk.Restart.Trial.RootIndexed
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Lineage
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
public import Probability.Process.Stopping.Concurrent.Finite
public import Combinatorics.BranchingWalk.Population.Offspring

/-!
# Cap-stopped finite candidate populations

For a finite-selection rule R and cap c, capStoppedPopulation starts from
the singleton root and retains the first generation whose size exceeds c;
capStoppedStep empties the following generation.

## Public declarations

The declarations in
ProbabilityTheory.BranchingRandomWalk are capStoppedStep,
capStoppedPopulation, capStoppedPopulation_zero,
capStoppedPopulation_succ, capStoppedPopulation_depth,
capStoppedPopulation_succ_parent, capStoppedPopulation_adapted,
capStoppedPopulation_card_le_two_mul,
capStoppedPopulation_card_le_pow,
capStoppedPopulation_succ_eq_empty_of_crossed,
capStoppedPopulation_eq_population_of_growthTrialSuccess,
rootedCapStoppedPopulation, rootedCapStoppedPopulation_zero,
rootedCapStoppedPopulation_node_depth,
rootedCapStoppedPopulation_card_le_two_mul,
rootedCapStoppedPopulation_card_le_pow, and
rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess,
rootedCapStoppedPopulation_succ_subset. Under a two-child selection rule and
1≤c, the retained population satisfies
\[
  \#\operatorname{capStoppedPopulation}(n,\omega)\le 2c,
\]
including its first crossing generation. The root-indexed construction
rootedCapStoppedPopulation maps each retained local address below an
observable root address; rootedCapStoppedPopulation_succ_subset shows that
each next-generation address is a selected child of a retained address.
If $R$ is bounded by $b$ offspring per particle, the generation-$n$
population also satisfies
\[
  \#\operatorname{capStoppedPopulation}(n,\omega)\le b^n,
\]
and the same bound holds for its root-indexed image.
For a successful fixed-length trial, the cutoff preserves the complete
population through the endpoint:
\[
  \operatorname{growthTrialSuccess}(R,\ell,c,d,\omega)
  \;\Longrightarrow\;
  \operatorname{capStoppedPopulation}(R,c,d,\omega)
    = \operatorname{population}(R,d,\omega).
\]
For every retained rooted address $q$,
\[
  q\in\operatorname{rootedCapStoppedPopulation}(R,c,\omega,root,a)
  \;\Longrightarrow\;
  |q.2|=|root.2|+a.
\]
If $1\le c$, a successful rooted trial with lower target $\ell$ satisfies
\[
  \operatorname{growthTrialSuccess}
    (R,\ell,c,d,\lambda u\mapsto\omega(root.1,root.2++u))
  \;\Longrightarrow\;
  \ell\le \#\operatorname{rootedCapStoppedPopulation}(R,c,\omega,root,d).
\]
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The next state of a selected candidate, killed if its current population
has already crossed `cap`.  The crossing generation is retained, with its
size controlled by the one-step offspring bound. -/
noncomputable def capStoppedStep {α X : Type*} (R : Step.FiniteSelection α X)
    (cap : ℕ) : Finset (TreeNode α) × Mark α (Step α X) → Finset (TreeNode α) :=
  fun p => if cap < p.1.card then ∅ else StepSelection.grow R p.1 p.2

/-- A selected population run from one candidate root and killed after the
first generation whose size exceeds `cap`. -/
noncomputable def capStoppedPopulation {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ) :
    ℕ → Mark α (Step α X) → Finset (TreeNode α)
  | 0, _ => {[]}
  | n + 1, ω => capStoppedStep R cap
      (capStoppedPopulation R cap n ω, frontierMarks n ω)

@[simp] theorem capStoppedPopulation_zero {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : Mark α (Step α X)) : capStoppedPopulation R cap 0 ω = {[]} := rfl

@[simp] theorem capStoppedPopulation_succ {α X : Type*}
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : Mark α (Step α X)) :
    capStoppedPopulation R cap (n + 1) ω =
      capStoppedStep R cap
        (capStoppedPopulation R cap n ω, frontierMarks n ω) := rfl

theorem capStoppedPopulation_depth {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : Mark α (Step α X)) :
    ∀ n u, u ∈ capStoppedPopulation R cap n ω → u.length = n := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simpa [capStoppedPopulation] using hu
  | succ n ih =>
      intro q hq
      simp only [capStoppedPopulation_succ, capStoppedStep] at hq
      split at hq
      · simp at hq
      · obtain ⟨u, hu, i, hi, rfl⟩ :=
          (StepSelection.mem_grow_iff R
            (capStoppedPopulation R cap n ω) (frontierMarks n ω) q).mp hq
        rw [List.length_append, ih u hu]
        simp

theorem capStoppedPopulation_succ_parent {α X : Type*}
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : Mark α (Step α X)) (q : TreeNode α)
    (hq : q ∈ capStoppedPopulation R cap (n + 1) ω) :
    ∃ u ∈ capStoppedPopulation R cap n ω, ∃ i,
      i ∈ R (ω u) ∧ q = u ++ [i] := by
  simp only [capStoppedPopulation_succ, capStoppedStep] at hq
  split at hq
  · simp at hq
  · obtain ⟨u, hu, i, hi, hqeq⟩ :=
      (StepSelection.mem_grow_iff R
        (capStoppedPopulation R cap n ω) (frontierMarks n ω) q).mp hq
    have hdepth := capStoppedPopulation_depth R cap ω n u hu
    have hfrontier : frontierMarks n ω u = ω u := by
      simp [frontierMarks, hdepth]
    exact ⟨u, hu, i, hfrontier ▸ hi, hqeq⟩

/-- The stopped candidate is measurable at each generation in the domain
filtration.  This proof uses only the measurability of the finite selection;
it does not inspect future success or failure outcomes. -/
theorem capStoppedPopulation_adapted {α X : Type*}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap : ℕ) :
    ∀ n, Measurable[generationFiltration (M := Step α X) n]
      (capStoppedPopulation R cap n) := by
  refine frontier_causal_state_adapted
    (capStoppedPopulation R cap) (capStoppedStep R cap) ?_ measurable_const ?_
  · classical
    have hcard : Measurable
        (fun p : Finset (TreeNode α) × Mark α (Step α X) => p.1.card) :=
      (measurable_of_countable fun s : Finset (TreeNode α) => s.card).comp
        measurable_fst
    have hcross : MeasurableSet
        {p : Finset (TreeNode α) × Mark α (Step α X) | cap < p.1.card} :=
      hcard measurableSet_Ioi
    exact Measurable.ite hcross measurable_const
      (StepSelection.grow_measurable R hR)
  · intro n ω
    rfl

/-- A two-child rule gives the advertised factor-two bound at every age,
including the first cap-crossing generation. -/
theorem capStoppedPopulation_card_le_two_mul {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (hR : R.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (ω : Mark α (Step α X)) :
    ∀ n, (capStoppedPopulation R cap n ω).card ≤ 2 * cap := by
  intro n
  induction n with
  | zero =>
      simp [capStoppedPopulation]
      omega
  | succ n ih =>
      simp only [capStoppedPopulation_succ, capStoppedStep]
      by_cases hcross : cap < (capStoppedPopulation R cap n ω).card
      · simp [hcross]
      · simp [hcross]
        have hprevious : (capStoppedPopulation R cap n ω).card ≤ cap :=
          Nat.le_of_not_gt hcross
        calc
          (StepSelection.grow R (capStoppedPopulation R cap n ω)
              (frontierMarks n ω)).card ≤
              2 * (capStoppedPopulation R cap n ω).card :=
            StepSelection.grow_card_le_mul R 2 hR _ _
          _ ≤ 2 * cap := Nat.mul_le_mul_left 2 hprevious

/-- If `R` is bounded by `b` selected children per particle, a cap-stopped trial
has at most `b ^ n` particles at generation `n`. -/
theorem capStoppedPopulation_card_le_pow {α X : Type*}
    (R : Step.FiniteSelection α X) (cap b : ℕ)
    (hR : R.IsBoundedBy b) (ω : Mark α (Step α X)) :
    ∀ n, (capStoppedPopulation R cap n ω).card ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp [capStoppedPopulation]
  | succ n ih =>
      simp only [capStoppedPopulation_succ, capStoppedStep]
      by_cases hcross : cap < (capStoppedPopulation R cap n ω).card
      · simp [hcross]
      · simp [hcross]
        calc
          (StepSelection.grow R (capStoppedPopulation R cap n ω)
              (frontierMarks n ω)).card ≤
              b * (capStoppedPopulation R cap n ω).card :=
            StepSelection.grow_card_le_mul R b hR _ _
          _ ≤ b * b ^ n := Nat.mul_le_mul_left b ih
          _ = b ^ (n + 1) := by rw [pow_succ]; ring

/-- Once a cap crossing has occurred, the next candidate generation is
empty. -/
theorem capStoppedPopulation_succ_eq_empty_of_crossed {α X : Type*}
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : Mark α (Step α X))
    (hcross : cap < (capStoppedPopulation R cap n ω).card) :
    capStoppedPopulation R cap (n + 1) ω = ∅ := by
  simp [capStoppedPopulation_succ, capStoppedStep, hcross]

/-- If the ordinary fixed-length growth trial succeeds, the cap-stopped
version with cap `upper` agrees with it through the endpoint. The cap is
checked before each growth step, so the strict pre-endpoint bounds from
`growthTrialSuccess` suffice. -/
theorem capStoppedPopulation_eq_population_of_growthTrialSuccess
    {α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (lower upper duration : ℕ)
    (ω : Mark α (Step α X)) (hupper : 1 ≤ upper)
    (hsuccess : growthTrialSuccess R lower upper duration ω) :
    capStoppedPopulation R upper duration ω =
      StepSelection.population R duration ω := by
  have hpre : ∀ k < duration,
      (StepSelection.population R k ω).card ≤ upper := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa using hupper
    · let j : Fin (duration - 1) := ⟨k - 1, by omega⟩
      have hj := hsuccess.2.2 j
      have hindex : j.val + 1 = k := by simp [j]; omega
      rw [hindex] at hj
      exact Nat.le_of_lt hj.2
  have hmain : ∀ n ≤ duration,
      capStoppedPopulation R upper n ω = StepSelection.population R n ω := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
        intro hle
        have hn : n < duration := by omega
        rw [capStoppedPopulation_succ, capStoppedStep, ih (by omega)]
        have hnot : ¬ upper < (StepSelection.population R n ω).card :=
          Nat.not_lt.mpr (hpre n hn)
        rw [ite_eq_right hnot, StepSelection.population_succ]
  exact hmain duration le_rfl

/-- The cap-stopped trial below a random root address, represented by its
absolute root-indexed genealogical addresses. -/
noncomputable def rootedCapStoppedPopulation
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) (age : ℕ) :
    Finset (RootIndexed.TreeNode Root α) :=
  (capStoppedPopulation R cap age
    (fun u => ω root.1 (root.2 ++ u))).map
      ⟨fun u => (root.1, root.2 ++ u), fun u v huv => by
        have htail : root.2 ++ u = root.2 ++ v := congrArg Prod.snd huv
        exact List.append_cancel_left htail⟩

@[simp] theorem rootedCapStoppedPopulation_zero {Root α X : Type*}
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) :
    rootedCapStoppedPopulation R cap ω root 0 = {root} := by
  classical
  ext p
  simp only [rootedCapStoppedPopulation, capStoppedPopulation,
    Finset.mem_map, Finset.mem_singleton]
  constructor
  · rintro ⟨u, hu, hpu⟩
    subst u
    change (root.1, root.2 ++ ([] : TreeNode α)) = p at hpu
    calc
      p = (root.1, root.2 ++ ([] : TreeNode α)) := hpu.symm
      _ = root := by cases root; simp [List.append_nil]
  · intro hp
    subst p
    refine ⟨[], by simp, ?_⟩
    change (root.1, root.2 ++ ([] : TreeNode α)) = root
    cases root
    simp [List.append_nil]

/-- Every node of a rooted cap-stopped candidate has its expected absolute
generation. -/
theorem rootedCapStoppedPopulation_node_depth
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root q : RootIndexed.TreeNode Root α) (age : ℕ)
    (hq : q ∈ rootedCapStoppedPopulation R cap ω root age) :
    q.2.length = root.2.length + age := by
  classical
  rw [rootedCapStoppedPopulation, Finset.mem_map] at hq
  obtain ⟨u, hu, hqeq⟩ := hq
  have haddr : q.2 = root.2 ++ u := by
    have h := congrArg Prod.snd hqeq
    change (root.2 ++ u) = q.2 at h
    exact h.symm
  rw [haddr, List.length_append]
  rw [capStoppedPopulation_depth R cap
    (fun v => ω root.1 (root.2 ++ v)) age u hu]

theorem rootedCapStoppedPopulation_card_le_two_mul
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (hR : R.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) (age : ℕ) :
    (rootedCapStoppedPopulation R cap ω root age).card ≤ 2 * cap := by
  simp only [rootedCapStoppedPopulation, Finset.card_map]
  exact capStoppedPopulation_card_le_two_mul R cap hR hcap
    (fun u => ω root.1 (root.2 ++ u)) age

/-- A successful fixed-length growth trial contributes at least its requested
endpoint population to the corresponding rooted cap-stopped population. -/
theorem rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (lower upper duration : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) (hupper : 1 ≤ upper)
    (hsuccess : growthTrialSuccess R lower upper duration
      (fun v => ω root.1 (root.2 ++ v))) :
    lower ≤ (rootedCapStoppedPopulation R upper ω root duration).card := by
  have htrial := capStoppedPopulation_eq_population_of_growthTrialSuccess
    R lower upper duration (fun v => ω root.1 (root.2 ++ v)) hupper hsuccess
  rw [rootedCapStoppedPopulation, Finset.card_map, htrial]
  exact hsuccess.1

/-- The root-indexed image of a cap-stopped trial with `R.IsBoundedBy b`
has at most `b ^ age` particles. -/
theorem rootedCapStoppedPopulation_card_le_pow
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap b : ℕ)
    (hR : R.IsBoundedBy b)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) (age : ℕ) :
    (rootedCapStoppedPopulation R cap ω root age).card ≤ b ^ age := by
  simp only [rootedCapStoppedPopulation, Finset.card_map]
  exact capStoppedPopulation_card_le_pow R cap b hR
    (fun u => ω root.1 (root.2 ++ u)) age

/-- The rooted stopped population is a genuine source: every retained address
in the next generation is a selected child of a retained current address.
Empty offspring are permitted, including after a cap crossing. -/
theorem rootedCapStoppedPopulation_succ_subset {Root α X : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) :
    ↑(rootedCapStoppedPopulation R cap ω root (n + 1)) ⊆
      Combinatorics.Branching.Population.offspringAddressSet
        (↑(rootedCapStoppedPopulation R cap ω root n))
        (fun p => ↑(R (ω p.1 p.2))) := by
  classical
  rintro ⟨r', q⟩ hq
  simp only [rootedCapStoppedPopulation, Finset.mem_coe, Finset.mem_map] at hq
  obtain ⟨v, hv, hqeq⟩ := hq
  change (root.1, root.2 ++ v) = (r', q) at hqeq
  have hroot : r' = root.1 := by
    exact (congrArg Prod.fst hqeq).symm
  have haddr : q = root.2 ++ v := by
    exact (congrArg Prod.snd hqeq).symm
  subst r'
  subst q
  obtain ⟨u, hu, i, hi, hveq⟩ :=
    capStoppedPopulation_succ_parent R cap n
      (fun u => ω root.1 (root.2 ++ u)) v hv
  refine Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
    ⟨(root.1, root.2 ++ u), ?_, i, ?_, ?_⟩
  · simp only [rootedCapStoppedPopulation, Finset.mem_coe, Finset.mem_map]
    exact ⟨u, hu, rfl⟩
  · exact hi
  · simp [hveq, Combinatorics.UlamHarris.RootIndexed.childAddress]

end ProbabilityTheory.BranchingRandomWalk

end
