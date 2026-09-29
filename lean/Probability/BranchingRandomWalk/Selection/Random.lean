module

public import Combinatorics.BranchingWalk.Selection.NSelection.Basic
public import Mathlib.Probability.Kernel.Basic

/-!
# Random selection mechanisms

Environment-dependent selection interfaces on arbitrary set-valued populations, with
capacity laws and deterministic realizations.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

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

end ProbabilityTheory.BranchingRandomWalk.Selection

end
