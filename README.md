# Independent domination roots of cozero-divisor graphs

[Research note (PDF)](paper/paper.pdf) · [LaTeX source](paper/paper.tex) · [中文说明](README.zh-CN.md)

This research note and its Lean proofs address a question posed by B. A. Rather. Fix primes $p<q$. For each positive integer $m$, form the cozero-divisor graph of the residue ring `ℤ/(pᵐq)` and count its independent dominating sets by size. Which complex numbers occur as limits of the nonzero roots of these counting polynomials as $m$ grows? [Original enumeration](https://www.dmlett.com/archive/v13/DML24_v13_pp36-43.pdf) · [Rather’s limit-point question](https://doi.org/10.1134/S0037446626060194)

For `(p,q) = (2,3)`, the only nonzero root is `−m`, so there is no finite limit. For every other pair, the root sets converge in Hausdorff distance to the unit circle together with a discrete set outside it. The exterior points are transcendental and accumulate at every point of the circle. For `(2,5)`, the outermost limit is real and lies strictly between `−1.24923133` and `−1.24923131`.

## Read the proof

| Question | Entry point |
| --- | --- |
| How is the polynomial defined from the finite ring? | [GraphDefinition.lean](Lean/GraphDefinition.lean) sums over independent dominating sets. It also proves the exceptional case. |
| What does Lean prove about the limit set? | [CozeroCertificates.lean](Lean/CozeroCertificates.lean) states the graph-level results `graph_geometry` and `graph_limit_theorem`. |
| Which classical results are inputs? | [CozeroLimitTheorem.lean](Lean/CozeroLimitTheorem.lean) states the unit-coefficient version of Fuchs’s sector theorem. [CozeroMahler.lean](Lean/CozeroMahler.lean) states the required value theorem for the Fredholm series. |
| How do zeros of the limit function persist in the finite polynomials? | [CozeroLocalZeros.lean](Lean/CozeroLocalZeros.lean) uses the maximum-modulus principle on a reciprocal. |

The exceptional case has no external theorem parameter. The geometry theorem takes Fuchs’s result as an explicit hypothesis. Transcendence additionally uses Mahler’s value theorem. The empirical zero-measure limit, the exact local multiplicity from Rouché’s theorem, and the full extremal-radius criterion have written proofs. The code verifies the [exponent-divisibility lemma](Lean/GapExponents.lean) used in the last criterion. [Source for the sector theorem, p. 515](https://msp.org/pjm/1972/43-2/pjm-v43-n2-p24-p.pdf) · [Source for the value theorem, p. 269](https://publi.math.unideb.hu/paper/4104/download/10_5486_PMD_1994_1437.pdf)

## Reproduce

Install Lean using [elan](https://leanprover-community.github.io/get_started.html). The project specifies Lean 4.19.0 and mathlib v4.19.0. On the first build, Lake needs internet access to obtain dependencies. From the repository root run

```sh
lake exe cache get
lake build
python check_cozero.py
```

The Python program uses the standard library. It compares all coefficients with direct graph enumeration for 15 small rings and verifies the `(2,5)` interval by rational arithmetic. The [verification log](verification.log) records a clean module-by-module Lean replay and the independent Python checks. The [file manifest](FILES.sha256) records SHA-256 digests.

## Provenance and license

OpenAI Codex contributed to problem selection, proof development, literature searches, formalization, verification, and writing. The [graph module notes](graph-provenance.txt) identify reused chain-arithmetic work. The code and its documentation use the [MIT License](LICENSE). The files in `paper/` use [Creative Commons Attribution 4.0 International](paper/LICENSE.md).
