/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Probability.RandomMeasure.Poisson.PointFamily.Basic

import Mathlib.Probability.Independence.Process.Basic

/-!
# Independence of Poisson point-family blocks

This module derives independence of disjoint coordinate subfamilies from the joint independence
field of a Poisson point family.

## Public declarations

- `IsPoissonPointFamily.measurable_pointFamilyCombined` states measurability of every encoded
  count or mark.
- `IsPoissonPointFamily.indepFun_pointFamily_split` states that injectively indexed subfamilies
  with disjoint images are independent, so
  $\operatorname{range}(\varphi)\cap\operatorname{range}(\psi)=\varnothing$ implies
  independence of the two processes
  $\operatorname{pointFamilyCombined}(K,X)\circ\varphi$ and
  $\operatorname{pointFamilyCombined}(K,X)\circ\psi$.
- `IsPoissonPointFamily.indepFun_count_marks` and
  `IsPoissonPointFamily.indepFun_piece_piece` give independence of a piece count from its marks
  and of the count-and-mark blocks belonging to distinct pieces.
- `IsPoissonPointFamily.indepFun_pieceBlocks` makes the blocks up to index $n$ independent of
  block $n+1$, using the coordinate-to-piece map `pointFamilyBlock` from `PointFamily.Basic`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-! ### Block independence of the point family

The counts and points of a piece `k` sit at combined-index positions `Sum.inl k` and
`Sum.inr (k, ·)`. Any two disjoint sets of combined-index positions carry independent sub-families,
by the joint `indep` field. The general splitting lemma below reads that independence off for two
arbitrary injections into the combined index whose images are disjoint; the count-versus-marks,
piece-versus-piece, and prefix-versus-next-block independences used by Campbell's formula, the
superposition step, and the compensated integral are all instances of it. -/

section BlockIndependence

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω}

/-- Every coordinate of the combined family is measurable: a count on `Sum.inl`, a point on
`Sum.inr`. -/
theorem IsPoissonPointFamily.measurable_pointFamilyCombined (hd : IsPoissonPointFamily K X m μ) :
    ∀ i, Measurable (pointFamilyCombined K X i)
  | Sum.inl k => hd.measurable_count k
  | Sum.inr p => hd.measurable_point p.1 p.2

/-- **Disjoint sub-families of the point family are independent.** For any two injections `φ`, `ψ`
into the combined index with disjoint images, the two processes obtained by reading the combined
family along `φ` and along `ψ` are independent. This is the single engine behind every
piece-block independence statement. -/
theorem IsPoissonPointFamily.indepFun_pointFamily_split [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {S T : Type} (φ : S → ℕ ⊕ ℕ × ℕ) (ψ : T → ℕ ⊕ ℕ × ℕ)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (hST : ∀ s t, φ s ≠ ψ t) :
    IndepFun (fun ω (i : S) => pointFamilyCombined K X (φ i) ω)
      (fun ω (j : T) => pointFamilyCombined K X (ψ j) ω) μ := by
  classical
  refine IndepFun.process_indepFun_process (fun i => hd.measurable_pointFamilyCombined (φ i))
    (fun j => hd.measurable_pointFamilyCombined (ψ j)) ?_
  intro I J
  set eφ : S ↪ ℕ ⊕ ℕ × ℕ := ⟨φ, hφ⟩ with heφ
  set eψ : T ↪ ℕ ⊕ ℕ × ℕ := ⟨ψ, hψ⟩ with heψ
  have hdisj : Disjoint (I.map eφ) (J.map eψ) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [Finset.mem_map] at hx1 hx2
    obtain ⟨a, -, rfl⟩ := hx1
    obtain ⟨c, -, hc⟩ := hx2
    exact hST a c hc.symm
  have key := hd.indep.indepFun_finset (I.map eφ) (J.map eψ) hdisj
    hd.measurable_pointFamilyCombined
  have hLmeas : Measurable
      (fun (g : (i : ↑(I.map eφ)) → pointFamilyIndexType E i.1) (i : I) =>
        g ⟨φ i, Finset.mem_map_of_mem eφ i.2⟩) :=
    Measurable.of_eval fun i => measurable_pi_apply _
  have hRmeas : Measurable
      (fun (g : (j : ↑(J.map eψ)) → pointFamilyIndexType E j.1) (j : J) =>
        g ⟨ψ j, Finset.mem_map_of_mem eψ j.2⟩) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  exact key.comp hLmeas hRmeas

/-- **Count-versus-marks independence within a piece.** For a fixed piece `k`, the count `K k` is
independent of the whole sequence of points `X k ·` of that piece. -/
theorem IsPoissonPointFamily.indepFun_count_marks [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (k : ℕ) :
    IndepFun (K k) (fun ω n => X k n ω) μ := by
  have h := hd.indepFun_pointFamily_split (S := Unit) (T := ℕ)
    (fun _ => Sum.inl k) (fun n => Sum.inr (k, n)) (fun _ _ _ => rfl)
    (fun a b hab => by simpa using hab) (fun _ _ => by simp)
  exact h.comp (φ := fun g : Unit → ℕ => g ()) (ψ := id)
    (measurable_pi_apply _) measurable_id

/-- **Piece-versus-piece independence.** For distinct pieces `j ≠ k`, the count-and-marks block
`(K j, X j ·)` is independent of the block `(K k, X k ·)`. Composing with a measurable functional of
each block yields, in particular, independence of the piece sums; see `indepFun_pieceSum_pieceSum`. -/
theorem IsPoissonPointFamily.indepFun_piece_piece [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {j k : ℕ} (hjk : j ≠ k) :
    IndepFun (fun ω => (K j ω, fun n => X j n ω)) (fun ω => (K k ω, fun n => X k n ω)) μ := by
  have hφinj : Function.Injective (Sum.elim (fun _ : Unit => Sum.inl j)
      (fun n : ℕ => Sum.inr (j, n)) : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ) := by
    rintro (a | a) (b | b) hab <;> simp_all
  have hψinj : Function.Injective (Sum.elim (fun _ : Unit => Sum.inl k)
      (fun n : ℕ => Sum.inr (k, n)) : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ) := by
    rintro (a | a) (b | b) hab <;> simp_all
  have hST : ∀ (s t : Unit ⊕ ℕ),
      (Sum.elim (fun _ : Unit => Sum.inl j) (fun n : ℕ => Sum.inr (j, n)) s)
        ≠ (Sum.elim (fun _ : Unit => Sum.inl k) (fun n : ℕ => Sum.inr (k, n)) t) := by
    rintro (s | s) (t | t) <;> simp [hjk]
  have h := hd.indepFun_pointFamily_split (S := Unit ⊕ ℕ) (T := Unit ⊕ ℕ)
    (Sum.elim (fun _ => Sum.inl j) (fun n => Sum.inr (j, n)))
    (Sum.elim (fun _ => Sum.inl k) (fun n => Sum.inr (k, n))) hφinj hψinj hST
  have hextrL : Measurable
      (fun g : (i : Unit ⊕ ℕ) → pointFamilyIndexType E
          (Sum.elim (fun _ => Sum.inl j) (fun n => Sum.inr (j, n)) i) =>
        (g (Sum.inl ()), fun n => g (Sum.inr n))) :=
    (measurable_pi_apply (Sum.inl ())).prodMk
      (Measurable.of_eval fun n => measurable_pi_apply (Sum.inr n))
  have hextrR : Measurable
      (fun g : (i : Unit ⊕ ℕ) → pointFamilyIndexType E
          (Sum.elim (fun _ => Sum.inl k) (fun n => Sum.inr (k, n)) i) =>
        (g (Sum.inl ()), fun n => g (Sum.inr n))) :=
    (measurable_pi_apply (Sum.inl ())).prodMk
      (Measurable.of_eval fun n => measurable_pi_apply (Sum.inr n))
  exact h.comp hextrL hextrR

/-- **Prefix-versus-next-block independence.** The whole family of counts and points belonging to
pieces `0, …, n` (packaged as one process over the combined-index positions with block index `≤ n`)
is independent of the count-and-marks block of piece `n + 1` (the positions with block index
`n + 1`). A functional of the first `n + 1` pieces is a measurable function of the left process, so
this yields independence of any statistic of pieces `≤ n` from any statistic of piece `n + 1`. -/
theorem IsPoissonPointFamily.indepFun_pieceBlocks [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (n : ℕ) :
    IndepFun
      (fun ω (i : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i ≤ n}) => pointFamilyCombined K X i.1 ω)
      (fun ω (i : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i = n + 1}) => pointFamilyCombined K X i.1 ω)
      μ :=
  hd.indepFun_pointFamily_split (S := {i // pointFamilyBlock i ≤ n})
    (T := {i // pointFamilyBlock i = n + 1}) Subtype.val Subtype.val Subtype.val_injective
    Subtype.val_injective (fun s t h => by
      have h1 := s.2; have h2 := t.2; rw [h] at h1; omega)

end BlockIndependence


end ProbabilityTheory
