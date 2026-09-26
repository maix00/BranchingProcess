import Combinatorics.BranchingWalk.Cloud.Basic
import Mathlib.Data.Finset.Card
/-! Common imports and conventions for indexed cloud ranks. -/

namespace Combinatorics
namespace Branching

variable {Index : Type*}

/-- Finite rank on an explicitly ordered finite index set. -/
noncomputable def finsetRank [LinearOrder Index]
    (s : Finset Index) (q : Index) : ℕ :=
  (s.filter fun p => p < q).card

@[simp] theorem finsetRank_def [LinearOrder Index]
    (s : Finset Index) (q : Index) :
    finsetRank s q = (s.filter fun p => p < q).card := rfl

theorem finsetRank_mem_lt_card [LinearOrder Index]
    {s : Finset Index} {q : Index} (hq : q ∈ s) :
    finsetRank s q < s.card := by
  unfold finsetRank
  exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨q, hq, lt_irrefl q⟩)

end Branching
end Combinatorics
