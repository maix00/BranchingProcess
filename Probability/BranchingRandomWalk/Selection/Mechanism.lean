import Combinatorics.BranchingWalk.Selection.NSelection.Basic
import Mathlib.Probability.Kernel.Basic

/-!
# Random and causal selection mechanisms

A deterministic `FiniteMechanism` sees only a finite candidate set.  A
`RandomSelectMechanism` may additionally read a random environment, while
still retaining only candidates that were supplied.  A
`CausalSelectMechanism` is a time-indexed family whose rule at time `t` is
measurable for the information domain `ℱ t`.

This is the interface required by an adapted killed branching random walk.
The randomness may already live in a pre-sampled marked tree.  A kernel is
also exposed for composition with genuinely randomized constructions.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection

/-- A measurable environment-dependent selection rule on finite candidate
sets. Measurability is joint in the environment and candidate set. -/
structure RandomSelectMechanism (Ω ι : Type*)
    [MeasurableSpace Ω] [MeasurableSpace ι] where
  select : Ω → Finset ι → Finset ι
  subset : ∀ ω s, select ω s ⊆ s
  measurable_select : Measurable (fun p : Ω × Finset ι => select p.1 p.2)

namespace RandomSelectMechanism

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]

instance : CoeFun (RandomSelectMechanism Ω ι)
    (fun _ => Ω → Finset ι → Finset ι) :=
  ⟨RandomSelectMechanism.select⟩

theorem select_subset (R : RandomSelectMechanism Ω ι)
    (ω : Ω) (s : Finset ι) : R.select ω s ⊆ s :=
  R.subset ω s

/-- Applying a random mechanism to a measurable candidate set remains
measurable. -/
theorem measurable_apply (R : RandomSelectMechanism Ω ι)
    (candidates : Ω → Finset ι) (hcandidates : Measurable candidates) :
    Measurable (fun ω => R.select ω (candidates ω)) :=
  R.measurable_select.comp (measurable_id.prodMk hcandidates)

/-- A deterministic selection rule is the environment-independent special
case of a random rule. -/
def ofDeterministic (M : FiniteMechanism ι) (hM : Measurable M.select) :
    RandomSelectMechanism Ω ι where
  select _ := M.select
  subset _ := M.subset
  measurable_select := hM.comp measurable_snd

/-- On a countable measurable candidate type, every deterministic mechanism
has a canonical random-rule realization. -/
noncomputable def ofDeterministicCountable
    [Countable ι] [MeasurableSingletonClass ι]
    (M : FiniteMechanism ι) : RandomSelectMechanism Ω ι :=
  ofDeterministic M (measurable_of_countable M.select)

@[simp] theorem ofDeterministic_select (M : FiniteMechanism ι)
    (hM : Measurable M.select) (ω : Ω) (s : Finset ι) :
    (ofDeterministic (Ω := Ω) M hM).select ω s = M.select s :=
  rfl

/-- The deterministic kernel associated with an environment-dependent rule.
This does not add randomness; it packages the measurable rule for later
kernel composition. -/
noncomputable def kernel (R : RandomSelectMechanism Ω ι) :
    Kernel (Ω × Finset ι) (Finset ι) :=
  Kernel.deterministic (fun p => R.select p.1 p.2) R.measurable_select

end RandomSelectMechanism

/-- An environment-dependent selection rule that keeps exactly `min N s.card`
candidates. This is the random counterpart of deterministic `NSelection`. -/
structure RandomNSelection (Ω ι : Type*) (N : ℕ)
    [MeasurableSpace Ω] [MeasurableSpace ι]
    extends RandomSelectMechanism Ω ι where
  card_eq : ∀ ω s, (select ω s).card = min N s.card

namespace RandomNSelection

variable {Ω ι : Type*} {N : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace ι]

theorem select_card_le (R : RandomNSelection Ω ι N)
    (ω : Ω) (s : Finset ι) : (R.select ω s).card ≤ N :=
  (R.card_eq ω s).le.trans (min_le_left _ _)

@[simp] theorem select_card (R : RandomNSelection Ω ι N)
    (ω : Ω) (s : Finset ι) : (R.select ω s).card = min N s.card :=
  R.card_eq ω s

theorem select_eq_self_of_card_le (R : RandomNSelection Ω ι N)
    (ω : Ω) (s : Finset ι) (h : s.card ≤ N) : R.select ω s = s := by
  exact Finset.eq_of_subset_of_card_le (R.subset ω s)
    (by rw [R.card_eq, min_eq_right h])

/-- A deterministic capacity-`N` mechanism is the environment-independent
random capacity-`N` mechanism. -/
def ofDeterministic (M : FiniteNSelection ι N) (hM : Measurable M.select) :
    RandomNSelection Ω ι N where
  toRandomSelectMechanism :=
    RandomSelectMechanism.ofDeterministic M.toFiniteMechanism hM
  card_eq _ := M.card_eq

noncomputable def ofDeterministicCountable
    [Countable ι] [MeasurableSingletonClass ι]
    (M : FiniteNSelection ι N) : RandomNSelection Ω ι N :=
  ofDeterministic M (measurable_of_countable M.select)

end RandomNSelection

/-- A causal time-dependent selection rule. At each time, the random rule is
measurable for exactly the information domain available at that time. -/
structure CausalSelectMechanism (Time Ω ι : Type*)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomSelectMechanism Ω ι (ℱ t) inferInstance

namespace CausalSelectMechanism

variable {Time Ω ι : Type*} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

/-- The retained candidates at time `t`. -/
def select (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : Finset ι :=
  @RandomSelectMechanism.select Ω ι (ℱ t) inferInstance (R.rule t) ω s

theorem select_subset (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : R.select t ω s ⊆ s :=
  @RandomSelectMechanism.subset Ω ι (ℱ t) inferInstance (R.rule t) ω s

/-- A causal rule sends an observable candidate population to an observable
retained population in the same information domain. -/
theorem measurable_select (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (candidates : Ω → Finset ι)
    (hcandidates : @Measurable Ω (Finset ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) :=
  by
    let _ : MeasurableSpace Ω := ℱ t
    exact (R.rule t).measurable_apply candidates hcandidates

/-- A fixed deterministic mechanism is causal for every information domain. -/
def ofDeterministic (M : FiniteMechanism ι) (hM : Measurable M.select) :
  CausalSelectMechanism Time Ω ι ℱ where
  rule t := @RandomSelectMechanism.ofDeterministic Ω ι (ℱ t) _ M hM

end CausalSelectMechanism

/-- A causal random selection rule with the uniform population cap `N`. -/
structure CausalNSelection (Time Ω ι : Type*) (N : ℕ)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomNSelection Ω ι N (ℱ t) inferInstance

namespace CausalNSelection

variable {Time Ω ι : Type*} {N : ℕ} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

def select (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : Finset ι :=
  @RandomSelectMechanism.select Ω ι (ℱ t) inferInstance
    (@RandomNSelection.toRandomSelectMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)) ω s

theorem select_subset (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : R.select t ω s ⊆ s :=
  @RandomSelectMechanism.subset Ω ι (ℱ t) inferInstance
    (@RandomNSelection.toRandomSelectMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)) ω s

theorem select_card_le (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (R.select t ω s).card ≤ N :=
  @RandomNSelection.select_card_le Ω ι N (ℱ t) inferInstance (R.rule t) ω s

@[simp] theorem select_card (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (R.select t ω s).card = min N s.card :=
  @RandomNSelection.card_eq Ω ι N (ℱ t) inferInstance (R.rule t) ω s

theorem select_eq_self_of_card_le (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) (h : s.card ≤ N) :
    R.select t ω s = s :=
  @RandomNSelection.select_eq_self_of_card_le Ω ι N (ℱ t) inferInstance
    (R.rule t) ω s h

theorem measurable_select (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (candidates : Ω → Finset ι)
    (hcandidates : @Measurable Ω (Finset ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) := by
  let _ : MeasurableSpace Ω := ℱ t
  simpa [select] using
    (@RandomNSelection.toRandomSelectMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)).measurable_apply candidates hcandidates

/-- A deterministic `NSelection` is causal for every information domain. -/
def ofDeterministic (M : FiniteNSelection ι N) (hM : Measurable M.select) :
    CausalNSelection Time Ω ι N ℱ where
  rule t := @RandomNSelection.ofDeterministic Ω ι N (ℱ t) _ M hM

end CausalNSelection

end ProbabilityTheory.BranchingRandomWalk.Selection
