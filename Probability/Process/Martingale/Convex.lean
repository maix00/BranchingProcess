/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Convex transformations of martingales

Conditional Jensen's inequality turns a martingale into a submartingale after
applying a convex function. The same argument gives norm and monotone-convex
specializations for martingales and submartingales.

Assume the transformed process is integrable, as in the theorem hypotheses.
For a martingale `X`, the martingale identity and conditional Jensen give the
first line below. For a submartingale `Y`, monotonicity followed by conditional
Jensen gives the second line:

\[
\begin{aligned}
\varphi(X_i)
&=\varphi\!\left(\mathbb E[X_j\mid\mathcal F_i]\right)
\leq \mathbb E[\varphi(X_j)\mid\mathcal F_i],\\
\varphi(Y_i)
&\leq \varphi\!\left(\mathbb E[Y_j\mid\mathcal F_i]\right)
\leq \mathbb E[\varphi(Y_j)\mid\mathcal F_i],
\qquad i\leq j.
\]

These relations hold almost surely. Here `φ : E → ℝ` is convex and
continuous, and in the second line it is also monotone. The norm theorem is
the first line with `φ(x)=‖x‖`.

## Public declarations

* `Martingale.submartingale_convex_comp`: if `X` is a martingale and `φ` is
  convex and continuous, then `φ ∘ X` is a submartingale whenever its values
  are integrable.
* `Martingale.submartingale_norm`: the norm of a Banach-valued martingale is a
  submartingale.
* `Submartingale.monotone_convex_comp`: a monotone convex continuous
  transformation of a submartingale is a submartingale when its values are
  integrable.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {ι Ω E : Type*} [PartialOrder ι] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → E}
  {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration μ ℱ]

/-- Composition of a martingale with a convex continuous function is a
submartingale, provided the transformed process is integrable. -/
theorem Martingale.submartingale_convex_comp (hX : Martingale X ℱ μ)
    {φ : E → ℝ} (hφ_cvx : ConvexOn ℝ Set.univ φ)
    (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω => φ (X t ω)) μ) :
    Submartingale (fun t ω => φ (X t ω)) ℱ μ := by
  refine ⟨fun i => hφ_cont.comp_stronglyMeasurable (hX.stronglyAdapted i),
    fun i j hij => ?_, hφ_int⟩
  calc
    _ =ᵐ[μ] fun ω => φ (μ[X j | ℱ i] ω) :=
      hX.condExp_ae_eq hij |>.fun_comp φ |>.symm
    _ ≤ᵐ[μ] μ[fun ω => φ (X j ω) | ℱ i] :=
      hφ_cvx.map_condExp_le_univ (ℱ.le i) hφ_cont.lowerSemicontinuous
        (hX.integrable j) (hφ_int j)

/-- The norm of a Banach-valued martingale is a submartingale. -/
theorem Martingale.submartingale_norm (hX : Martingale X ℱ μ) :
    Submartingale (fun t ω => ‖X t ω‖) ℱ μ :=
  hX.submartingale_convex_comp convexOn_univ_norm continuous_norm
    (fun i => (hX.integrable i).norm)

variable [Preorder E] {Y : ι → Ω → E}

/-- A monotone convex continuous function sends an integrable submartingale to
a submartingale. -/
theorem Submartingale.monotone_convex_comp (hY : Submartingale Y ℱ μ)
    {φ : E → ℝ} (hφ_mono : Monotone φ)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω => φ (Y t ω)) μ) :
    Submartingale (fun t ω => φ (Y t ω)) ℱ μ := by
  refine ⟨fun i => hφ_cont.comp_stronglyMeasurable (hY.stronglyAdapted i),
    fun i j hij => ?_, hφ_int⟩
  calc
    _ ≤ᵐ[μ] fun ω => φ (μ[Y j | ℱ i] ω) :=
      (hY.ae_le_condExp hij).mono fun ω hω => hφ_mono hω
    _ ≤ᵐ[μ] μ[fun ω => φ (Y j ω) | ℱ i] :=
      hφ_cvx.map_condExp_le_univ (ℱ.le i) hφ_cont.lowerSemicontinuous
        (hY.integrable j) (hφ_int j)

end MeasureTheory

end
