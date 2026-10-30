/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.InfiniteOffspring.Repair

/-!
# The repaired selection subadditive array

For \(0<N\), write \(\omega_s(t)=\omega(s+t)\). Then
`repairedInfiniteSelectionSubadditiveArray` defines
\[
  A_\omega(s,n)=-\left[
    \operatorname{measurableRepairedInfiniteOffspringRun}
      \ n\ \bigl(\mathbf 0,\omega_s\bigr)
  \right]_0,
\]
the negative position of rank zero after \(n\) steps from zero in the
environment segment beginning at generation \(s\).

## Public declarations

The single public declaration is the function \(A_\omega(s,n)\) defined
above.

## Source

The block variable \(X_{m,n}=-\min W_{m,n-m}\) is defined in the proof of
WANG Yiyang, *Asymptotic Speed of the \(N\)-Branching Random Walk with Infinite
Offspring*, Master's thesis, Fudan University (2026), Section 3.4.2,
Lemma 3.12. This definition stores its negative minimum as an array indexed
by a starting generation and a block length.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

noncomputable def repairedInfiniteSelectionSubadditiveArray {N : ℕ}
    (hN : 0 < N) (ω : GenerationEnvironment N)
    (start length : ℕ) : ℝ :=
  - measurableRepairedInfiniteOffspringRun length
      ((fun _ : Fin N => (0 : ℝ)), fun t => ω (start + t)) ⟨0, hN⟩
end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
