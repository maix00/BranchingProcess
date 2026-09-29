module

public import Combinatorics.BranchingWalk.Selection.NSelection.Basic
public import Mathlib.Probability.Kernel.Basic

/-!
# Finite-input selection mechanisms

Environment-dependent selection interfaces on finite candidate sets, including the
deterministic kernel adapter.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection

open Combinatorics.Branching.Selection

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

end ProbabilityTheory.BranchingRandomWalk.Selection

end
