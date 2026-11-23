/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Kernel
public import Probability.Kernel.IonescuTulcea.Map

/-!
# Measurable factors of state-dependent branching processes

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `generationKernel_map` proves that `K(s).map (Step.map f) = L(f(s))`
  implies the same identity for the whole next generation.
* `generationPathLaw_map` gives the full path-law identity with any joint
  initial root distribution: mapping every state by `f` gives the process
  with offspring kernel `L` and the mapped initial distribution.
* `treeKernel_map` gives the single-tree version:
  `Pᴷ_s.map (t ↦ (u ↦ (t u).map f)) = Pᴸ_(s.map f)`.

States are arbitrary measurable spaces; the measurable factor need not be
injective. This uses the existing native product and Ionescu--Tulcea laws.
For the use in Zhan Shi, *Branching Random Walks* (2015), §4.5, proof of
Theorem 4.3 preceding (4.12), take `f = Sum.inl` to identify the complete
normal subtree with the original branching process,
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

variable {S T α : Type*} [MeasurableSpace S] [MeasurableSpace T]

/-- An offspring-kernel factor commutes with independent reproduction of the whole population. -/
theorem generationKernel_map {Root : Type*}
    (K : Kernel S (Step α S)) (L : Kernel T (Step α T))
    [IsMarkovKernel K] [IsMarkovKernel L]
    (f : S → T) (hf : Measurable f)
    (hstep : ∀ s, (K s).map (Step.map f) = L (f s))
    (n : ℕ) (s : (Root × (Fin n → α)) → Option S) :
    (generationKernel K n s).map (fun next p => (next p).map f) =
      generationKernel L n (fun p => (s p).map f) := by
  have hopt : Measurable (Option.map f) := measurable_option_map hf
  have hbrood : Measurable (Step.map (ι := α) f) := Step.map_measurable hf
  let μ (p : Root × (Fin n → α)) :=
    Kernel.optionElim (Measure.dirac (fun _ : α => (none : Option S))) K (s p)
  let ν (p : Root × (Fin n → α)) :=
    Kernel.optionElim (Measure.dirac (fun _ : α => (none : Option T))) L ((s p).map f)
  have hm (p) : (μ p).map (Step.map f) = ν p := by
    dsimp [μ, ν]
    cases he : s p with
    | none =>
      simp only [Option.map_none, Kernel.optionElim_none,
        Measure.map_dirac' (Step.map_measurable hf)]
      rfl
    | some a =>
      simp only [Option.map_some, Kernel.optionElim_some]
      exact hstep a
  have hprod : (Measure.infinitePi μ).map (fun broods p => Step.map f (broods p)) =
      Measure.infinitePi ν := by
    rw [Measure.infinitePi_map_pi μ (fun _ => Step.map_measurable hf)]
    simp_rw [hm]
  rw [generationKernel_apply, generationKernel_apply,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.infinitePi μ).map _ = (Measure.infinitePi ν).map _
  rw [← hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- State factors transport the actual process law, including a joint random initial population. -/
theorem generationPathLaw_map {Root : Type*}
    (K : Kernel S (Step α S)) (L : Kernel T (Step α T))
    [IsMarkovKernel K] [IsMarkovKernel L]
    (f : S → T) (hf : Measurable f)
    (hstep : ∀ s, (K s).map (Step.map f) = L (f s))
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial] :
    (generationPathLaw K initial).map (fun x n p => (x n p).map f) =
      generationPathLaw L (initial.map (fun x r => (x r).map f)) := by
  have hopt : Measurable (Option.map f) := measurable_option_map hf
  have hpop (n : ℕ) : Measurable
      (fun x : (Root × (Fin n → α)) → Option S => fun p => (x p).map f) :=
    measurable_pi_iff.mpr fun p => (measurable_option_map hf).comp (measurable_pi_apply p)
  rw [generationPathLaw, Kernel.map_trajMeasure
    (generationHistoryKernel K) (generationHistoryKernel L)
    (fun n (x : (Root × (Fin n → α)) → Option S) p => (x p).map f) hpop]
  · rw [generationPathLaw, Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  · intro n history
    exact generationKernel_map K L f hf hstep n (history ⟨n, by simp⟩)

private theorem pathKernel_map
    (K : Kernel S (Step α S)) (L : Kernel T (Step α T))
    [IsMarkovKernel K] [IsMarkovKernel L]
    (f : S → T) (hf : Measurable f)
    (hstep : ∀ s, (K s).map (Step.map f) = L (f s)) (s : Option S) :
    (pathKernel K s).map (fun x n p => (x n p).map f) = pathKernel L (s.map f) := by
  have hopt : Measurable (Option.map f) := measurable_option_map hf
  rw [pathKernel_eq_generationPathLaw,
    generationPathLaw_map K L f hf hstep, Measure.map_dirac' (by fun_prop),
    pathKernel_eq_generationPathLaw]

/-- Applying a measurable state factor to the canonical whole tree gives the factored tree law. -/
theorem treeKernel_map
    (K : Kernel S (Step α S)) (L : Kernel T (Step α T))
    [IsMarkovKernel K] [IsMarkovKernel L]
    (f : S → T) (hf : Measurable f)
    (hstep : ∀ s, (K s).map (Step.map f) = L (f s)) (s : Option S) :
    (treeKernel K s).map (fun t u => (t u).map f) = treeKernel L (s.map f) := by
  have hopt : Measurable (Option.map f) := measurable_option_map hf
  rw [treeKernel, treeKernel, Kernel.map_apply _ (by fun_prop),
    Kernel.map_apply _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    ← pathKernel_map K L f hf hstep s, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end ProbabilityTheory.BranchingProcess.State

end
