import Combinatorics.BranchingWalk.Selection.NSelection.Basic
import Mathlib.Probability.Kernel.Basic

/-!
# Random and causal selection mechanisms

The short names act on arbitrary set-valued candidate populations.  Their
`Finite` counterparts are implementation interfaces for finite candidate
sets.  Random rules may read the ambient environment, and causal rules at
time `t` are measurable for exactly the information domain `ℱ t`.

This is the interface required by an adapted killed branching random walk.
The randomness may already live in a pre-sampled marked tree.  A kernel is
also exposed for composition with genuinely randomized constructions.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection

/-! ### General set-valued selection -/

/-- An environment-dependent selection rule on an arbitrary candidate set.
No countability or finiteness assumption is imposed on the candidate type. -/
structure RandomSelectMechanism (Ω ι : Type*)
    [MeasurableSpace Ω] [MeasurableSpace ι] where
  select : Ω → Set ι → Set ι
  subset : ∀ ω s, select ω s ⊆ s
  measurable_select : Measurable (fun p : Ω × Set ι => select p.1 p.2)

namespace RandomSelectMechanism

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]

instance : CoeFun (RandomSelectMechanism Ω ι)
    (fun _ => Ω → Set ι → Set ι) :=
  ⟨RandomSelectMechanism.select⟩

theorem select_subset (R : RandomSelectMechanism Ω ι)
    (ω : Ω) (s : Set ι) : R.select ω s ⊆ s :=
  R.subset ω s

/-- Environment-dependent pointwise selection.  This is random killing when
`keep ω` is the set of states or particles that survive in environment
`ω`; it remains an ordinary selection mechanism rather than a parallel
notion. -/
def filter (keep : Ω → Set ι) (hkeep : Measurable keep) :
    RandomSelectMechanism Ω ι where
  select ω s := {q ∈ s | q ∈ keep ω}
  subset _ _ q hq := hq.1
  measurable_select := by
    rw [measurable_set_iff]
    intro q
    exact ((measurable_pi_apply q).comp measurable_snd).and
      ((measurable_pi_apply q).comp (hkeep.comp measurable_fst))

@[simp] theorem mem_filter (keep : Ω → Set ι) (hkeep : Measurable keep)
    (ω : Ω) (s : Set ι) (q : ι) :
    q ∈ (filter keep hkeep).select ω s ↔ q ∈ s ∧ q ∈ keep ω :=
  Iff.rfl

theorem measurable_apply (R : RandomSelectMechanism Ω ι)
    (candidates : Ω → Set ι) (hcandidates : Measurable candidates) :
    Measurable (fun ω => R.select ω (candidates ω)) :=
  R.measurable_select.comp (measurable_id.prodMk hcandidates)

/-- A deterministic arbitrary-set mechanism is a constant random mechanism. -/
def ofDeterministic (M : Mechanism ι) (hM : Measurable M.select) :
    RandomSelectMechanism Ω ι where
  select _ := M.select
  subset _ := M.subset
  measurable_select := hM.comp measurable_snd

end RandomSelectMechanism

/-- A random capacity selection from an arbitrary candidate set. -/
structure RandomNSelection (Ω ι : Type*) (N : ℕ)
    [MeasurableSpace Ω] [MeasurableSpace ι] where
  select : Ω → Set ι → Finset ι
  subset : ∀ ω s q, q ∈ select ω s → q ∈ s
  card_finite : ∀ ω s, ∀ h : s.Finite,
    (select ω s).card = min N h.toFinset.card
  card_infinite : ∀ ω s, s.Infinite → (select ω s).card = N
  measurable_select : Measurable (fun p : Ω × Set ι => select p.1 p.2)

namespace RandomNSelection

variable {Ω ι : Type*} {N : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace ι]

/-- Forget the capacity law and coerce the finite output to a set. -/
def toRandomSelectMechanism (R : RandomNSelection Ω ι N)
    (hcoe : Measurable ((↑) : Finset ι → Set ι)) :
    RandomSelectMechanism Ω ι where
  select ω s := ↑(R.select ω s)
  subset := R.subset
  measurable_select := hcoe.comp R.measurable_select

theorem select_card_le (R : RandomNSelection Ω ι N)
    (ω : Ω) (s : Set ι) : (R.select ω s).card ≤ N := by
  rcases s.finite_or_infinite with h | h
  · rw [R.card_finite ω s h]
    exact min_le_left _ _
  · rw [R.card_infinite ω s h]

def ofDeterministic (M : NSelection ι N) (hM : Measurable M.select) :
    RandomNSelection Ω ι N where
  select _ := M.select
  subset _ := M.subset
  card_finite _ := M.card_finite
  card_infinite _ := M.card_infinite
  measurable_select := hM.comp measurable_snd

end RandomNSelection

/-- A time-indexed arbitrary-set selection rule adapted to the domain flow. -/
structure CausalSelectMechanism (Time Ω ι : Type*)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomSelectMechanism Ω ι (ℱ t) inferInstance

namespace CausalSelectMechanism

variable {Time Ω ι : Type*} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

def select (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : Set ι :=
  @RandomSelectMechanism.select Ω ι (ℱ t) inferInstance (R.rule t) ω s

theorem select_subset (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : R.select t ω s ⊆ s :=
  @RandomSelectMechanism.subset Ω ι (ℱ t) inferInstance (R.rule t) ω s

theorem measurable_select (R : CausalSelectMechanism Time Ω ι ℱ)
    (t : Time) (candidates : Ω → Set ι)
    (hcandidates : @Measurable Ω (Set ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Set ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) := by
  let _ : MeasurableSpace Ω := ℱ t
  exact (R.rule t).measurable_apply candidates hcandidates

def ofDeterministic (M : Mechanism ι) (hM : Measurable M.select) :
    CausalSelectMechanism Time Ω ι ℱ where
  rule t := @RandomSelectMechanism.ofDeterministic Ω ι (ℱ t) _ M hM

end CausalSelectMechanism

/-- A time-indexed capacity selection on arbitrary candidate sets. -/
structure CausalNSelection (Time Ω ι : Type*) (N : ℕ)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomNSelection Ω ι N (ℱ t) inferInstance

namespace CausalNSelection

variable {Time Ω ι : Type*} {N : ℕ} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

def select (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : Finset ι :=
  @RandomNSelection.select Ω ι N (ℱ t) inferInstance (R.rule t) ω s

theorem select_subset (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Set ι) :
    ∀ q ∈ R.select t ω s, q ∈ s :=
  @RandomNSelection.subset Ω ι N (ℱ t) inferInstance (R.rule t) ω s

theorem select_card_le (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Set ι) : (R.select t ω s).card ≤ N :=
  @RandomNSelection.select_card_le Ω ι N (ℱ t) inferInstance
    (R.rule t) ω s

theorem measurable_select (R : CausalNSelection Time Ω ι N ℱ)
    (t : Time) (candidates : Ω → Set ι)
    (hcandidates : @Measurable Ω (Set ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) := by
  let _ : MeasurableSpace Ω := ℱ t
  exact (R.rule t).measurable_select.comp (measurable_id.prodMk hcandidates)

def ofDeterministic (M : NSelection ι N) (hM : Measurable M.select) :
    CausalNSelection Time Ω ι N ℱ where
  rule t := @RandomNSelection.ofDeterministic Ω ι N (ℱ t) _ M hM

end CausalNSelection

/-! ### Finite-input implementations -/

/-- A measurable environment-dependent selection rule on finite candidate
sets. Measurability is joint in the environment and candidate set. -/
structure RandomFiniteMechanism (Ω ι : Type*)
    [MeasurableSpace Ω] [MeasurableSpace ι] where
  select : Ω → Finset ι → Finset ι
  subset : ∀ ω s, select ω s ⊆ s
  measurable_select : Measurable (fun p : Ω × Finset ι => select p.1 p.2)

namespace RandomFiniteMechanism

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]

instance : CoeFun (RandomFiniteMechanism Ω ι)
    (fun _ => Ω → Finset ι → Finset ι) :=
  ⟨RandomFiniteMechanism.select⟩

theorem select_subset (R : RandomFiniteMechanism Ω ι)
    (ω : Ω) (s : Finset ι) : R.select ω s ⊆ s :=
  R.subset ω s

/-- Applying a random mechanism to a measurable candidate set remains
measurable. -/
theorem measurable_apply (R : RandomFiniteMechanism Ω ι)
    (candidates : Ω → Finset ι) (hcandidates : Measurable candidates) :
    Measurable (fun ω => R.select ω (candidates ω)) :=
  R.measurable_select.comp (measurable_id.prodMk hcandidates)

/-- A deterministic selection rule is the environment-independent special
case of a random rule. -/
def ofDeterministic (M : FiniteMechanism ι) (hM : Measurable M.select) :
    RandomFiniteMechanism Ω ι where
  select _ := M.select
  subset _ := M.subset
  measurable_select := hM.comp measurable_snd

/-- On a countable measurable candidate type, every deterministic mechanism
has a canonical random-rule realization. -/
noncomputable def ofDeterministicCountable
    [Countable ι] [MeasurableSingletonClass ι]
    (M : FiniteMechanism ι) : RandomFiniteMechanism Ω ι :=
  ofDeterministic M (measurable_of_countable M.select)

@[simp] theorem ofDeterministic_select (M : FiniteMechanism ι)
    (hM : Measurable M.select) (ω : Ω) (s : Finset ι) :
    (ofDeterministic (Ω := Ω) M hM).select ω s = M.select s :=
  rfl

/-- The deterministic kernel associated with an environment-dependent rule.
This does not add randomness; it packages the measurable rule for later
kernel composition. -/
noncomputable def kernel (R : RandomFiniteMechanism Ω ι) :
    Kernel (Ω × Finset ι) (Finset ι) :=
  Kernel.deterministic (fun p => R.select p.1 p.2) R.measurable_select

end RandomFiniteMechanism

/-- An environment-dependent selection rule that keeps exactly `min N s.card`
candidates. This is the random counterpart of deterministic `NSelection`. -/
structure RandomFiniteNSelection (Ω ι : Type*) (N : ℕ)
    [MeasurableSpace Ω] [MeasurableSpace ι]
    extends RandomFiniteMechanism Ω ι where
  card_eq : ∀ ω s, (select ω s).card = min N s.card

namespace RandomFiniteNSelection

variable {Ω ι : Type*} {N : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace ι]

theorem select_card_le (R : RandomFiniteNSelection Ω ι N)
    (ω : Ω) (s : Finset ι) : (R.select ω s).card ≤ N :=
  (R.card_eq ω s).le.trans (min_le_left _ _)

@[simp] theorem select_card (R : RandomFiniteNSelection Ω ι N)
    (ω : Ω) (s : Finset ι) : (R.select ω s).card = min N s.card :=
  R.card_eq ω s

theorem select_eq_self_of_card_le (R : RandomFiniteNSelection Ω ι N)
    (ω : Ω) (s : Finset ι) (h : s.card ≤ N) : R.select ω s = s := by
  exact Finset.eq_of_subset_of_card_le (R.subset ω s)
    (by rw [R.card_eq, min_eq_right h])

/-- A deterministic capacity-`N` mechanism is the environment-independent
random capacity-`N` mechanism. -/
def ofDeterministic (M : FiniteNSelection ι N) (hM : Measurable M.select) :
    RandomFiniteNSelection Ω ι N where
  toRandomFiniteMechanism :=
    RandomFiniteMechanism.ofDeterministic M.toFiniteMechanism hM
  card_eq _ := M.card_eq

noncomputable def ofDeterministicCountable
    [Countable ι] [MeasurableSingletonClass ι]
    (M : FiniteNSelection ι N) : RandomFiniteNSelection Ω ι N :=
  ofDeterministic M (measurable_of_countable M.select)

end RandomFiniteNSelection

/-- A causal time-dependent selection rule. At each time, the random rule is
measurable for exactly the information domain available at that time. -/
structure CausalFiniteMechanism (Time Ω ι : Type*)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomFiniteMechanism Ω ι (ℱ t) inferInstance

namespace CausalFiniteMechanism

variable {Time Ω ι : Type*} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

/-- The retained candidates at time `t`. -/
def select (R : CausalFiniteMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : Finset ι :=
  @RandomFiniteMechanism.select Ω ι (ℱ t) inferInstance (R.rule t) ω s

theorem select_subset (R : CausalFiniteMechanism Time Ω ι ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : R.select t ω s ⊆ s :=
  @RandomFiniteMechanism.subset Ω ι (ℱ t) inferInstance (R.rule t) ω s

/-- A causal rule sends an observable candidate population to an observable
retained population in the same information domain. -/
theorem measurable_select (R : CausalFiniteMechanism Time Ω ι ℱ)
    (t : Time) (candidates : Ω → Finset ι)
    (hcandidates : @Measurable Ω (Finset ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) :=
  by
    let _ : MeasurableSpace Ω := ℱ t
    exact (R.rule t).measurable_apply candidates hcandidates

/-- A fixed deterministic mechanism is causal for every information domain. -/
def ofDeterministic (M : FiniteMechanism ι) (hM : Measurable M.select) :
  CausalFiniteMechanism Time Ω ι ℱ where
  rule t := @RandomFiniteMechanism.ofDeterministic Ω ι (ℱ t) _ M hM

end CausalFiniteMechanism

/-- A causal random selection rule with the uniform population cap `N`. -/
structure CausalFiniteNSelection (Time Ω ι : Type*) (N : ℕ)
    [MeasurableSpace ι] (ℱ : Time → MeasurableSpace Ω) where
  rule : ∀ t, @RandomFiniteNSelection Ω ι N (ℱ t) inferInstance

namespace CausalFiniteNSelection

variable {Time Ω ι : Type*} {N : ℕ} [MeasurableSpace ι]
    {ℱ : Time → MeasurableSpace Ω}

def select (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : Finset ι :=
  @RandomFiniteMechanism.select Ω ι (ℱ t) inferInstance
    (@RandomFiniteNSelection.toRandomFiniteMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)) ω s

theorem select_subset (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) : R.select t ω s ⊆ s :=
  @RandomFiniteMechanism.subset Ω ι (ℱ t) inferInstance
    (@RandomFiniteNSelection.toRandomFiniteMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)) ω s

theorem select_card_le (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (R.select t ω s).card ≤ N :=
  @RandomFiniteNSelection.select_card_le Ω ι N (ℱ t) inferInstance (R.rule t) ω s

@[simp] theorem select_card (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) :
    (R.select t ω s).card = min N s.card :=
  @RandomFiniteNSelection.card_eq Ω ι N (ℱ t) inferInstance (R.rule t) ω s

theorem select_eq_self_of_card_le (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (ω : Ω) (s : Finset ι) (h : s.card ≤ N) :
    R.select t ω s = s :=
  @RandomFiniteNSelection.select_eq_self_of_card_le Ω ι N (ℱ t) inferInstance
    (R.rule t) ω s h

theorem measurable_select (R : CausalFiniteNSelection Time Ω ι N ℱ)
    (t : Time) (candidates : Ω → Finset ι)
    (hcandidates : @Measurable Ω (Finset ι) (ℱ t) inferInstance candidates) :
    @Measurable Ω (Finset ι) (ℱ t) inferInstance
      (fun ω => R.select t ω (candidates ω)) := by
  let _ : MeasurableSpace Ω := ℱ t
  simpa [select] using
    (@RandomFiniteNSelection.toRandomFiniteMechanism Ω ι N (ℱ t) inferInstance
      (R.rule t)).measurable_apply candidates hcandidates

/-- A deterministic `NSelection` is causal for every information domain. -/
def ofDeterministic (M : FiniteNSelection ι N) (hM : Measurable M.select) :
    CausalFiniteNSelection Time Ω ι N ℱ where
  rule t := @RandomFiniteNSelection.ofDeterministic Ω ι N (ℱ t) _ M hM

end CausalFiniteNSelection

end ProbabilityTheory.BranchingRandomWalk.Selection
