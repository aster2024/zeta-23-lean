# Suggested arXiv metadata

## Title

An Explicit Four-Point Improvement to the Unconditional Montgomery--Taylor Bound for Simple Zeta Zeros

## Authors

Jizhou Guo

## Primary category

`math.NT` (Number Theory)

## Cross-list

`math.FA` is optional because the proof uses Hermitian trace inequalities, but the central result is number theory. Do not cross-list to computer science solely because Lean is used.

## License

Recommended: arXiv's non-exclusive license to distribute. This preserves future journal flexibility. CC BY 4.0 is also viable if broad reuse is preferred, but it is not necessary for submission.

## Comments field

```text
17 pages. Companion to the unconditional trace-and-pair-correlation framework of Claude (2026). Includes Lean formalization and exact rational certificates; code and verification artifacts are linked in the paper.
```

## Abstract

```text
Let N(T,2T) count nontrivial zeros of the Riemann zeta function with T < Im rho <= 2T, with multiplicity, and let N_0^s(T,2T) count those zeros that are simple and lie on the critical line. Building on the unconditional trace-and-pair-correlation framework of Claude, whose optimized endpoint constant is H_* = 0.672500703679..., we prove liminf N_0^s(T,2T)/N(T,2T) >= H_* + 1/79828975. The new ingredient is a width-six, four-point packing argument. We localize small values of the normalized Montgomery--Taylor kernel near its first six positive zeros, prove an exact three-coordinate energy lower bound, and combine the double counting of six Gram edges with a sharp trace-zero four-block inequality. Every terminal comparison is rational. The full extension, including the fixed-window transfer and endpoint passage, is checked in Lean at a pinned public commit; executable ledgers independently enumerate all 216 root-index budgets. We also determine the ceiling of this frozen finite interface: the next unit fraction 1/79828974 cannot be obtained without strengthening at least one of its inputs.
```

This metadata version deliberately uses plain ASCII and no display-math
delimiters; paste it directly into arXiv's abstract field.

## Certification wording

Use "formally verified at a pinned public commit" rather than "literature-established" or "independently accepted." The repository build and audit are evidence of formal consistency, not a substitute for journal peer review.
