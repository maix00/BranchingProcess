import ThesisSpeed.Probability.Genealogy.Reserve.Lineages
import ThesisSpeed.Probability.Genealogy.MultiRoot.Filtration

/-!
# Reserve lineages for every initial root

The two indices are the initial-root label and the reserve-trial label. Each
lineage is again pre-sampled, its path is adapted to the multi-root
filtration, and its visible split generation is a stopping time.
-/

open MeasureTheory

namespace ThesisSpeed

/-- Pre-sampled reserve lineages for every labelled initial root. The two
indices are the initial-root label and the reserve-trial label. -/
structure MultiRootReserveLineages (m : ℕ) where
  path : Fin m → ℕ → ℕ → MultiRootMark m → 𝕍
  step : Fin m → ℕ → 𝕍 × NatRealBranchingStep → 𝕍
  measurable_step : ∀ i k, Measurable (step i k)
  measurable_root : ∀ i k,
    Measurable[multiRootFiltration m 0] (path i k 0)
  depth : ∀ i k n ω, (path i k n ω).length = n
  recursion : ∀ i k n ω,
    path i k (n + 1) ω =
      step i k (path i k n ω, ω i (path i k n ω))

theorem MultiRootReserveLineages.path_adapted {m : ℕ}
    (r : MultiRootReserveLineages m) (i : Fin m) (k : ℕ) :
    ∀ n, Measurable[multiRootFiltration m n] (r.path i k n) := by
  intro n
  induction n with
  | zero => exact r.measurable_root i k
  | succ n ih =>
      have hold : Measurable[multiRootFiltration m (n + 1)]
          (r.path i k n) :=
        ih.mono (multiRootFiltration m |>.mono (Nat.le_succ n)) le_rfl
      have hmark : Measurable[multiRootFiltration m (n + 1)]
          (fun ω : MultiRootMark m => ω i (r.path i k n ω)) :=
        multiRootSelectedMark_measurable i (r.path i k n) hold
          (fun ω => by rw [r.depth i k n ω]; exact Nat.lt_succ_self n)
      have hpair : Measurable[multiRootFiltration m (n + 1)]
          (fun ω : MultiRootMark m =>
            (r.path i k n ω, ω i (r.path i k n ω))) :=
        hold.prodMk hmark
      convert (r.measurable_step i k).comp hpair using 1
      funext ω
      exact r.recursion i k n ω

def multiRootSplitDeclaration {m : ℕ}
    (i : Fin m) (path : ℕ → MultiRootMark m → 𝕍) :
    ℕ → Set (MultiRootMark m)
  | 0 => ∅
  | n + 1 => {ω | ω i (path n ω) ∈ twoChildren}

noncomputable def MultiRootReserveLineages.sigma {m : ℕ}
    (r : MultiRootReserveLineages m) (i : Fin m) (k : ℕ) :
    MultiRootMark m → WithTop ℕ :=
  firstDeclaredSuccess (multiRootSplitDeclaration i (r.path i k))

theorem MultiRootReserveLineages.sigma_isStoppingTime {m : ℕ}
    (r : MultiRootReserveLineages m) (i : Fin m) (k : ℕ) :
    IsStoppingTime (multiRootFiltration m) (r.sigma i k) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  cases n with
  | zero =>
      exact (multiRootFiltration m 0).measurableSet_empty
  | succ n =>
      have hold : Measurable[multiRootFiltration m (n + 1)]
          (r.path i k n) :=
        (r.path_adapted i k n).mono
          (multiRootFiltration m |>.mono (Nat.le_succ n)) le_rfl
      exact (multiRootSelectedMark_measurable i (r.path i k n) hold
        (fun ω => by rw [r.depth i k n ω]; exact Nat.lt_succ_self n))
          twoChildren_measurable

theorem MultiRootReserveLineages.all_sigma_isStoppingTime {m : ℕ}
    (r : MultiRootReserveLineages m) :
    ∀ i k, IsStoppingTime (multiRootFiltration m) (r.sigma i k) :=
  r.sigma_isStoppingTime

end ThesisSpeed
