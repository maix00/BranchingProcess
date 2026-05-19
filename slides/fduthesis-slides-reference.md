# fduthesis slides: equation tag mapping & Assumption 6 dependency chain

## Equation tag mapping (thesis .dtx label → rendered PDF tag)
- eq:4.1 → Eq.(3.1)
- eq:4.2 → Eq.(3.2)
- eq:4.3 → Eq.(3.3)
- eq:4.3:2 → Eq.(3.4)
- eq:4.6 → Eq.(3.6)
- eq:4.7 → Eq.(3.7)
- eq:4.8 → Eq.(3.8)
- eq:4.9 → Eq.(3.9)
- eq:4.10 → Eq.(3.10)
- eq:4.11 → Eq.(3.11)
- eq:4.11:tilde → Eq.(3.12)

## Lemma mapping (thesis .dtx label → rendered PDF tag)
- lemma:4.1 → Lemma 3.4
- lemma:2.3 → Lemma 3.5
- lemma:4.2 → Lemma 3.6
- lemma:4.3 → Lemma 3.7
- lemma:4.5 → Lemma 3.8
- lemma:4.6 → Lemma 3.9
- lemma:4.7 → Lemma 3.10
- lemma:4.8 → Lemma 3.17

## Assumption 6 (finite cross second moment) — PRECISE per-equation dependency chain
Formula: E[sum_{i≠j} e^{-(Ξ_i+Ξ_j)}] < ∞

DIRECTLY used in:
- Lemma 3.8 Eq.(3.14): cross term Σ(z^i)Σ(z^j) bounded via Assumption 6

INDIRECTLY used in:
- Lemma 3.9 Eq.(3.7) (NOT Eq.3.8!): Paley–Zygmund → second moment → Lemma 3.8 Eq.(3.14) → Assumption 6
- Lemma 3.10 Eq.(3.9) (NOT Eq.3.10 or Eq.3.11!): Paley–Zygmund → Lemma 3.8 directly → Assumption 6 (NOTE: the thesis overview paragraph says "Lemma 4.6" but the actual proof uses Lemma 4.5/Lemma 3.8)
- Right-tail step 2 "Many particles at ℓ+": uses Lemma 3.9 Eq.(3.7) to bound P(#Z^k_{ℓN+}=0) → Assumption 6
- Right-tail step 2 "Few particles at ℓ+": uses Lemma 3.10 Eq.(3.9) via binomial + Chernoff → Assumption 6

NOT used in:
- Lemma 3.4–3.7 (spine walk lemmas)
- Lemma 3.17 (coupling)
- Lemma 3.9 Eq.(3.8) — only uses Lemma 4.2+4.3
- Lemma 3.10 Eq.(3.10) — standard random walk properties
- Lemma 3.10 Eq.(3.11) — only uses Lemma 4.1+4.3
- Right-tail step 1: Phase I uses Eq.(3.10), Bottleneck uses Eq.(3.11), Phase II uses Eq.(3.8) — NONE use Assumption 6

## 4th moment assumption
- E[(Ξ_1)_+^4] < ∞
- Used in:
  - Theorem 1.1 statement (stated as condition)
  - L² reduction: E[M_n^4] via 4th moment → Cauchy–Schwarz
  - Upper bound 3: Cauchy–Schwarz O(log³ N) (removable)
- Slides annotated:
  - Theorem 1.1 + L² reduction: "4th-moment control" in blue ✓
  - Upper bound 3: Note about O(log³N) in blue ✓

## Slide snippet files inventory
- right_tail_step1_tau.tex — Step 1: bound P(τ≤ℓ_N)
- right_tail_step2_mk.tex — Step 2: bound P(M^k ≥ ζ' log N)
- upper_bound_1.tex — Unified upper bound 1: coupling + bad event definition
- upper_bound_2.tex — Unified upper bound 2: restart definitions
- upper_bound_3.tex — Unified upper bound 3: bad event bound + Cauchy–Schwarz
- lemma_4_5_statement.tex — Lemma 3.8 statement
- lemma_4_6_statement.tex — Lemma 3.9 statement
- lemma_4_7_statement.tex — Lemma 3.10 statement
- lemma_4_8_role.tex — Lemma 3.17 coupling statement
- theorem_1_1_restate.tex — Theorem 1.1 restatement
