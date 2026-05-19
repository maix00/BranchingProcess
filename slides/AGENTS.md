# AGENTS.md — Slides change log

Each modification should be committed with a message prefixed by the commit hash.

---

## [06770e5] Rewrite defense script: per-slide paragraphs, full CN+EN
- Rewrite `script/defense_script.tex`: each slide group gets one Chinese paragraph + one English paragraph
- No page breaks between sections; 6 pages total
- Covers all slides: Opening → Background → Main Theorem → Upper bound → Lower bound → L² limit → Mogul'skii → Summary

## [b2c2df2] Add defense script
- Create `script/defense_script.tex`: bilingual (CN/EN) defense script covering all 36 slides
- 28 pages, covers: Opening → Background → Main Theorem → Upper bound → Lower bound → L² limit → Right/Left tail → Mogul'skii → Conclusion

## [11cdc9e] Add AGENTS.md, rename NUMBERING_MAP → fduthesis-slides-reference
- `AGENTS.md` created to track all slide modifications
- `NUMBERING_MAP.md` → `fduthesis-slides-reference.md` with full equation/lemma mapping + Assumption 6 chain

## [7e3f0c3] Rename BRW frame to $N$-BRW
- `main.tex`: frame title `BRW on the marked tree space` → `$N$-BRW on the marked tree space`

## [b0893f2] Refine N-BRW/BRW structure, add right-tail lemmas & proof snippets
- Swap N-BRW and BRW frame order; N-BRW first with selection mechanism
- Restore full BRW marked tree content (Ulam-Harris, marked trees, selection operator, position/speed)
- Add `part3_lemmas_summary.tex` with Δ/L notation and Eq. labels
- Add right-tail proof steps: `right_tail_a0.tex`, `right_tail_a1.tex`, `right_tail_a1a0.tex`, `right_tail_step1b_tau.tex`, `right_tail_step2b_mk.tex`
- Add `mogulskii_combined.tex`, `many_to_one_spine.tex`, `lemma_3_3.tex`, `part2_lemmas_summary.tex`, `left_tail_proof.tex`
- Tidy `right_tail_step1_tau.tex`, `right_tail_step2_mk.tex`, `lemma_4_8_role.tex`, `nbrw_def.tex`
- `brw_marked_tree.tex`: compact then restored full with selection operator + position/speed

## [9a184ef] Refine killed BRW construction and fix numbering

## [d9d8e5a] Reorder lower bound section, fix restart operator, simplify lower bound chain

## [4d50722] Expand upper bound conclusion with full t→∞ derivation chain from thesis

## [1d5c4b5] Reorder: L² version, proof given later; can be refined to L¹
