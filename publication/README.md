# Companion publication

This directory contains the source and exact evidence for

> Jizhou Guo, *An Explicit Four-Point Improvement to the Unconditional Montgomery--Taylor Bound for Simple Zeta Zeros*.

The manuscript proves the explicit increment `1/79,828,975` over the parent
unconditional Montgomery--Taylor endpoint.  This directory is the public,
hash-locked source snapshot synchronized from the submission-assurance
package.  Formal-kernel certification and external mathematical peer review
remain distinct; see `REPRODUCIBILITY.md` for the trust boundary.

## Contents

- `main.tex`, `references.bib`, `main.bbl`: paper source.
- `results/`: two exact rational ledgers, frozen outputs, and public CI receipt.
- `REPRODUCIBILITY.md`: fast rational check, pinned Lean check, and trust boundary.
- `ARXIV_SUBMISSION.md`: suggested plain-text arXiv metadata.
- `CHECKSUMS.sha256`: hashes of the publication files.

The compiled PDF and complete arXiv archive are distributed separately so the
formal source repository stays small.
