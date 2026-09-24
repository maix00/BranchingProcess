# Proof review and formalization status

## Theorems 1.1 and 1.2

The two statements have been checked against the arguments in Chapter 3, but
this is **not** a complete independent verification of every probabilistic
lemma. Three concrete errors in the written deductions were repaired:

1. In the proof of Theorem 1.1, squaring the endpoints of
   `[ζ, ζ′]` did not preserve their order when the limiting trajectory was
   negative. The second-moment sandwich now uses the infimum of `x²` on the
   interval and the maximum of the squared endpoints.
2. The appendix had `E[(V¹_n)₊] ≤ E[V¹_n]`, which is false for a signed
   position. It now uses `E[|V¹_n|] ≤ n E[|Ξ₁|]`.
3. The `a = 1` right-tail proof compared against `a = 1/2`, which does not
   work for every threshold just above the `a = 1` limit. It now chooses
   `b < 1` close enough to `1` for the given threshold.

The negative exponential moment bound `E[exp(-M_n)] ≤ 1` applies to a
single initial particle. For `m` initial particles it is `≤ m`. Theorem
1.1's fourth-moment step now shifts by `log N` and yields the uniform bound
`E[(M_n)₋⁴] = O(1 + (log N)⁴)` for `m ≤ N`.

**Remaining audit issue:** the transition estimate in the proof of the
tilted-tube lower bound (`contents/part-2-eng.tex`, event `E₀`) calls the
probability `O(1/Δ)` and then needs `≥ C/Δ`. The displayed lower bound
requires a stated lower local-limit or ballot theorem with its hypotheses
verified for the moving tube; weak convergence of the conditioned endpoint
alone does not supply the survival probability. This affects a key input to
both main theorems and still needs a complete reference or proof.

The proof of Theorem 1.2 also applies the appendix's fourth/second-moment
bound for an ordinary selected walk directly to the **restarted** process
`Vᵇ` when estimating `E[Mᵇ_{ℓ_N} 1_{E_Nᶜ}]` in
`contents/main-results/speed.tex`. The restarted process has a different law;
an independent moment bound for it or a justified comparison is needed. This
is a potentially substantive gap, so Theorem 1.2 has not been certified as
correct by this review.

## Proposed first-moment Theorem 1.3

The bilingual statement is in `contents/introduction/main-results.tex` and
retains the cross-term assumption. It removes only the fourth moment of the
positive part of `Ξ₁`. The original Theorem 1.1 remains an `L²` theorem with
its original moment assumptions.

**Theorem 1.3 is not yet proved in the thesis or Lean.** A pointwise
first-moment truncation inequality and the final analytic speed-limit step
are machine-checked in `lean/ThesisSpeed/Analytic.lean`. They do not supply
the one-sided `L¹` position estimates or the coupling on exceptional events.
In particular, simply replacing Cauchy--Schwarz by uniform integrability of
an `O((log N)³)`-step one-particle walk only gives `o((log N)³)`;
the proof needs `o(log N)` at that point. A sharper one-sided argument is
required before calling this a proved strengthening.

## Potential weakening of the cross-term condition

The current pair expectation directly controls the two-descendant term in
the second-moment proof. A condition only on the first child `Ξ₁` does not
control this expectation if the offspring count has a heavy tail. The
precise replacement condition therefore remains undecided. Mallein's
original speed theorem uses a different logarithmic weighted-offspring tail
condition, equation (1.9), rather than this pair moment; see the
[primary paper](https://arxiv.org/html/1503.03762v2). Its separate
assumption (1.10) controls the extremal child, and should not be confused
with (1.9). Neither has yet been shown sufficient for Theorem 1.1 here.

## Reuse in Lean

The pinned mathlib checkout provides filters, real limits, integration,
stochastic-process and martingale infrastructure. A search of that checkout
found no existing branching random walk, Galton--Watson, many-to-one, or
Mogul'skii module. Public search also found no ready-to-import Lean
formalization of this specific model. The related
[LeanLevy](https://github.com/slink/LeanLevy) and
[Stat-Lean](https://github.com/StatLean/Stat-Lean) libraries cover adjacent
probability machinery, not the missing branching-selection theorem.
