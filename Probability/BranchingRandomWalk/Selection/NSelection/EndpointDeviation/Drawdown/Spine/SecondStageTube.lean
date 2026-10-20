/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Window
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event

/-!
# Restarted second-stage tube events for killed capacity

The public declarations in namespace
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail` are:

For an increment sequence $x$, write $S_j(x)=\sum_{i<j}x_i$ and
$x^{(\ell)}_j=x_{\ell+j}$.

- `rightTailPositiveASecondStageWindow ell ellN κ c v j`: with
  $D=\ell_N-\ell$, $w=D^{1/3}$, and
  $d_j=(\kappa/c^2)D^{-2/3}j$, the window is $\{0\}$ at $j=0$,
  $[d_j,d_j+cw]$ for $0<j<D$, $[d_D,d_D+vw]$ when $0<j=D$, and empty
  after the terminal generation.
- `rightTailPositiveASecondStageTubeEvent ell ellN κ c v` is the set of paths
  whose displacement at every $j\in[0,D]$ lies in the corresponding window.
- `rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v` imposes the
  same window condition for every $j\in[0,d]$.
- `rightTailPositiveASecondStageTubeEvent_subset_fixedTube`: for $0\leq c$
  and $v\leq c$, the full tube event is contained in
  $\{x: \forall j\leq D,\ S_j(x)\in[d_j,d_j+cD^{1/3}]\}$.
- `rightTailPositiveASecondStageTubePrefixEvent_subset_fixedTube` gives the
  same corridor inclusion for every prefix $d\leq D$.
- `rightTailPositiveASecondStageTubeEvent_subset_drawdownEvent`: when
  $\ell<\ell_N$, $0\leq\kappa$, $0<c$, and $v\leq c$, the full tube
  event is contained in the generic drawdown event with horizon $D$, width
  $cD^{1/3}$, and endpoint ceiling $d_D+cD^{1/3}$.
- `rightTailPositiveASecondStageTubePrefixEvent_subset_drawdownEvent` gives
  this inclusion through each prefix $d\leq D$.
- `rightTailPositiveARestartedWindow_event_subset_shiftedSecondStageTubePrefix`:
  if $\ell<k\leq\ell_N$, membership in the restarted-window event
  through generation $k$ implies that the shifted increments
  $x^{(\ell)}$ belong to the second-stage tube prefix of length
  $k-\ell$.

These event constructions encode the restarted tube in the proof of the
positive-initial-mass estimate, Proposition 3.1, equation (4.15), of Elie
Aïdékon and Yueyun Hu, *Average-weight percolation on the complete graph*,
arXiv:2512.23266 (2025). The event inclusions are grouped here with the
objects they describe. The one-use probability comparison needed by the
capacity proof is in `Lemmas/Tube.lean`.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.RandomWalk

/-- The relative-generation interval used for the restarted second-stage
tube in Proposition 3.1, equation (4.15), of Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, arXiv:2512.23266 (2025). -/
noncomputable def rightTailPositiveASecondStageWindow
    (ell ellN : ℕ) (κ c v : ℝ) (j : ℕ) : Set ℝ :=
  let D := ellN - ell
  let width := ((D : ℕ) : ℝ) ^ (3⁻¹ : ℝ)
  if j = 0 then Set.Icc 0 0
  else if j < D then
    Set.Icc (rightTailPositiveADrift ell ellN κ c j)
      (rightTailPositiveADrift ell ellN κ c j + c * width)
  else if j = D then
    Set.Icc (rightTailPositiveADrift ell ellN κ c j)
      (rightTailPositiveADrift ell ellN κ c j + v * width)
  else ∅

/-- Paths whose displacement at each time through the restart horizon belongs
to the corresponding second-stage window in Proposition 3.1, equation
(4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the
complete graph*, arXiv:2512.23266 (2025). -/
noncomputable def rightTailPositiveASecondStageTubeEvent
    (ell ellN : ℕ) (κ c v : ℝ) : Set (ℕ → ℝ) :=
  {increment | ∀ j : Fin (ellN - ell + 1),
    AdditivePath.displacement (j : ℕ) increment ∈
      rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)}

/-- Paths whose displacement satisfies the second-stage window conditions
through a specified prefix. This event is used in the prefix comparison for
Proposition 3.1, equation (4.15), of Elie Aïdékon and Yueyun Hu,
*Average-weight percolation on the complete graph*, arXiv:2512.23266 (2025). -/
noncomputable def rightTailPositiveASecondStageTubePrefixEvent
    (ell ellN d : ℕ) (κ c v : ℝ) : Set (ℕ → ℝ) :=
  {increment | ∀ j : Fin (d + 1),
    AdditivePath.displacement (j : ℕ) increment ∈
      rightTailPositiveASecondStageWindow ell ellN κ c v (j : ℕ)}

/-- The variable-width second-stage tube is contained in a fixed-width
increasing tube whenever the terminal window is no wider than the interior
window. -/
lemma rightTailPositiveASecondStageTubeEvent_subset_fixedTube
    (ell ellN : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hc : 0 ≤ c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubeEvent ell ellN κ c v ⊆
      {increment : ℕ → ℝ | ∀ j : Fin (ellN - ell + 1),
        AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))} := by
  intro increment hpath j
  let D := ellN - ell
  let width : ℝ := (D : ℝ) ^ (3⁻¹ : ℝ)
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hwidth : 0 ≤ width := by positivity
  have hterminal : v * width ≤ c * width :=
    mul_le_mul_of_nonneg_right hvc hwidth
  by_cases hjzero : (j : ℕ) = 0
  · have hj : j = 0 := Fin.ext hjzero
    subst j
    simp [rightTailPositiveADrift, D, width, mul_nonneg hc hwidth]
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
    by_cases hjlt : (j : ℕ) < D
    · have hmember := hpath j
      simpa [rightTailPositiveASecondStageWindow, D, width,
        hjzero, hjlt] using hmember
    · have hjEq : (j : ℕ) = D := by
        have hjle : (j : ℕ) ≤ D := Nat.le_of_lt_succ j.isLt
        omega
      have hmember := hpath j
      have hmember' : AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width) := by
        simpa [rightTailPositiveASecondStageWindow, D, width,
          hjzero, hjlt, hjEq, hDpos.ne'] using hmember
      have hupper :
          rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width ≤
            rightTailPositiveADrift ell ellN κ c (j : ℕ) + c * width := by
        linarith [hterminal]
      exact ⟨hmember'.1,
        hmember'.2.trans (by simpa [D, width] using hupper)⟩

/-- Every initial segment of the second-stage tube is contained in the
corresponding fixed-width increasing tube, including the narrower terminal
window when the segment reaches `ellN`. -/
lemma rightTailPositiveASecondStageTubePrefixEvent_subset_fixedTube
    (ell ellN d : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hd : d ≤ ellN - ell)
    (hc : 0 ≤ c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v ⊆
      {increment : ℕ → ℝ | ∀ j : Fin (d + 1),
        AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))} := by
  intro increment hpath j
  let D := ellN - ell
  let width : ℝ := (D : ℝ) ^ (3⁻¹ : ℝ)
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hwidth : 0 ≤ width := by positivity
  have hterminal : v * width ≤ c * width :=
    mul_le_mul_of_nonneg_right hvc hwidth
  by_cases hjzero : (j : ℕ) = 0
  · have hj : j = 0 := Fin.ext hjzero
    subst j
    simp [rightTailPositiveADrift, D, width, mul_nonneg hc hwidth]
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
    have hjleD : (j : ℕ) ≤ D := by
      exact (Nat.le_of_lt_succ j.isLt).trans hd
    by_cases hjlt : (j : ℕ) < D
    · have hmember := hpath j
      simpa [rightTailPositiveASecondStageTubePrefixEvent,
        rightTailPositiveASecondStageWindow, D, width, hjzero, hjlt]
        using hmember
    · have hjEq : (j : ℕ) = D := by omega
      have hmember := hpath j
      have hmember' : AdditivePath.displacement (j : ℕ) increment ∈
          Set.Icc (rightTailPositiveADrift ell ellN κ c (j : ℕ))
            (rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width) := by
        simpa [rightTailPositiveASecondStageTubePrefixEvent,
          rightTailPositiveASecondStageWindow, D, width,
          hjzero, hjlt, hjEq, hDpos.ne'] using hmember
      have hupper :
          rightTailPositiveADrift ell ellN κ c (j : ℕ) + v * width ≤
            rightTailPositiveADrift ell ellN κ c (j : ℕ) + c * width := by
        linarith [hterminal]
      exact ⟨hmember'.1,
        hmember'.2.trans (by simpa [D, width] using hupper)⟩

/-- The whole second-stage tube event implies the drawdown event with the
same width as its interior corridor. The increasing linear drift is why a
path can gain height without increasing its drawdown allowance. -/
lemma rightTailPositiveASecondStageTubeEvent_subset_drawdownEvent
    (ell ellN : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubeEvent ell ellN κ c v ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        (ellN - ell)
        (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
        (rightTailPositiveADrift ell ellN κ c (ellN - ell) +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) := by
  let D := ellN - ell
  let drift : ℕ → ℝ := rightTailPositiveADrift ell ellN κ c
  let width : ℝ := c * (((D : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hcoef : 0 ≤ κ / c ^ 2 * (D : ℝ) ^ ((-2 : ℝ) / 3) := by
    positivity
  have hmono : Monotone drift := by
    intro i j hij
    dsimp [drift, rightTailPositiveADrift]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hcoef
  have hwidth : 0 ≤ width := by
    dsimp [width]
    positivity
  have hcontained := rightTailPositiveASecondStageTubeEvent_subset_fixedTube
    ell ellN κ c v hellN hc.le hvc
  intro increment hpath
  have hpositions : ∀ j : Fin (D + 1),
      AdditivePath.displacement (j : ℕ) increment ∈
        Set.Icc (drift (j : ℕ)) (drift (j : ℕ) + width) := by
    simpa [D, drift, width] using hcontained hpath
  have hdrawdown :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_mem_noLargeDropEndpointBelowEvent_of_monotoneCorridor
    D drift width hmono increment hpositions
  simpa [D, drift, width] using hdrawdown



/-- A second-stage prefix of length `d` is contained in a drawdown event at
that same horizon. The corridor scale still uses the full planned horizon
`ellN - ell`. -/
lemma rightTailPositiveASecondStageTubePrefixEvent_subset_drawdownEvent
    (ell ellN d : ℕ) (κ c v : ℝ)
    (hellN : ell < ellN) (hd : d ≤ ellN - ell)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvc : v ≤ c) :
    rightTailPositiveASecondStageTubePrefixEvent ell ellN d κ c v ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        d
        (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
        (rightTailPositiveADrift ell ellN κ c d +
          c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) := by
  let D := ellN - ell
  let drift : ℕ → ℝ := rightTailPositiveADrift ell ellN κ c
  let width : ℝ := c * (((D : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hDpos : 0 < D := by dsimp [D]; exact Nat.sub_pos_of_lt hellN
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hcoef : 0 ≤ κ / c ^ 2 * (D : ℝ) ^ ((-2 : ℝ) / 3) := by
    positivity
  have hmono : Monotone drift := by
    intro i j hij
    dsimp [drift, rightTailPositiveADrift]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hcoef
  have hcontained := rightTailPositiveASecondStageTubePrefixEvent_subset_fixedTube
    ell ellN d κ c v hellN hd hc.le hvc
  intro increment hpath
  have hpositions : ∀ j : Fin (d + 1),
      AdditivePath.displacement (j : ℕ) increment ∈
        Set.Icc (drift (j : ℕ)) (drift (j : ℕ) + width) := by
    simpa [D, drift, width] using hcontained hpath
  have hdrawdown :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_mem_noLargeDropEndpointBelowEvent_of_monotoneCorridor
    d drift width hmono increment hpositions
  simpa [D, drift, width] using hdrawdown

/-- After the restart time, membership in the original window schedule
forces the corresponding shifted increments to stay in the second-stage
tube through the observed prefix. -/
lemma rightTailPositiveARestartedWindow_event_subset_shiftedSecondStageTubePrefix
    (ell ellN k : ℕ) (logN b v c κ : ℝ)
    (hk : ell < k) (hkN : k ≤ ellN) :
    {increment : ℕ → ℝ |
      InRestartedWindows ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (history k 0 increment)} ⊆
      {increment : ℕ → ℝ |
        (fun j => increment (ell + j)) ∈
          rightTailPositiveASecondStageTubePrefixEvent
            ell ellN (k - ell) κ c v} := by
  intro increment hwindow j
  change InRestartedWindows ell
    (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    (history k 0 increment) at hwindow
  have hellN : ell < ellN := lt_of_lt_of_le hk hkN
  have hEllNe : ellN ≠ ell := Ne.symm hellN.ne
  have hDpos : 0 < ellN - ell := Nat.sub_pos_of_lt hellN
  have hDadd : ell + (ellN - ell) = ellN := by omega
  by_cases hjzero : (j : ℕ) = 0
  · have hj : j = 0 := Fin.ext hjzero
    subst j
    simp [rightTailPositiveASecondStageWindow, AdditivePath.displacement_zero]
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hjzero
    have hleftBound : ell < k + 1 := by omega
    have hrightBound : ell + (j : ℕ) < k + 1 := by
      have hjle : (j : ℕ) ≤ k - ell := Nat.le_of_lt_succ j.isLt
      omega
    have hpath := hwindow ⟨ell + (j : ℕ), hrightBound⟩
    have hanchor : restartAnchor ell (ell + (j : ℕ)) = ell :=
      restartAnchor_eq_cutoff (by omega)
    have hpath' :
        history k 0 increment ⟨ell + (j : ℕ), hrightBound⟩ -
          history k 0 increment ⟨ell, hleftBound⟩ ∈
          rightTailPositiveARestartedWindow ell ellN logN b v c κ
            (ell + (j : ℕ)) := by
      simpa only [hanchor] using hpath
    have hshift :
        history k 0 increment ⟨ell + (j : ℕ), hrightBound⟩ -
          history k 0 increment ⟨ell, hleftBound⟩ =
        AdditivePath.displacement (j : ℕ) (fun q => increment (ell + q)) := by
      calc
        _ = AdditivePath.displacement (ell + (j : ℕ)) increment -
            AdditivePath.displacement ell increment := by
          simp [history_eq_fromIncrements, AdditivePath.fromIncrements]
        _ = AdditivePath.displacement (j : ℕ)
            (fun q => increment (ell + q)) := by
          rw [AdditivePath.displacement_add]
          ring
    rw [hshift] at hpath'
    by_cases hjterminal : (j : ℕ) = ellN - ell
    · have habsolute : ell + (j : ℕ) = ellN := by omega
      simpa [rightTailPositiveARestartedWindow,
        rightTailPositiveASecondStageTubePrefixEvent,
        rightTailPositiveASecondStageWindow, hjpos.ne', hjterminal,
        habsolute, hDpos.ne', hDadd, Nat.add_sub_cancel_left,
        not_lt_of_ge hellN.le, hEllNe] using hpath'
    · have hjlt : (j : ℕ) < ellN - ell := by omega
      have habsolute : ell + (j : ℕ) < ellN := by omega
      simpa [rightTailPositiveARestartedWindow,
        rightTailPositiveASecondStageTubePrefixEvent,
        rightTailPositiveASecondStageWindow, hjpos.ne', hjterminal,
        hjlt, habsolute, hDpos.ne', hDadd, Nat.add_sub_cancel_left,
        not_lt_of_ge hellN.le, hEllNe] using hpath'


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
