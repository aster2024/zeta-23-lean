# Reproducibility guide

## Fast exact-arithmetic check

From `publication/results/` (or simply this directory after changing into
`results/`) run:

```bash
python3 wider_four_point_rational_ledger.py --verify-frozen-output
python3 wider_fixed_interface_ceiling_ledger.py --verify-frozen-output
```

Expected terminal markers:

```text
WIDER_FOUR_POINT_RATIONAL_LEDGER PASS
WIDER_FIXED_INTERFACE_CEILING_LEDGER PASS
```

The first ledger also reads the five Lean source snapshots stored under
`sources/zeta-23-lean/`; these are the exact files bound by its parser.  Both
commands compare their output byte-for-byte with the frozen output files.

## Lean check

Clone the public repository and select the publication branch:

```bash
git clone https://github.com/aster2024/zeta-23-lean.git
cd zeta-23-lean
git checkout codex/wider-strict-improvement-79828975
git checkout d368cc49d689576c81d7e4df0c135057d2462a27
git rev-parse HEAD
```

The last command must print:

```text
d368cc49d689576c81d7e4df0c135057d2462a27
```

Then run the pinned build workflow described in `.github/workflows/wider-strict-improvement.yml`. The toolchain is Lean `v4.33.0-rc2`, with Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129`.

The publication snapshot's CI receipt is `results/receipt.json`. The
successful run is <https://github.com/aster2024/zeta-23-lean/actions/runs/31637227865>.

## Manuscript check

From `publication/` run:

```bash
tectonic --keep-logs --keep-intermediates main.tex
rg -n 'undefined|Citation|Reference|Overfull|Underfull' main.log
```

The final command should return no mathematical-reference or box warnings.

## Trust boundary

- Python checks terminal exact arithmetic, not analytic number theory.
- Lean checks the formal statements and their dependencies as encoded in the repository.
- The manuscript supplies the human mathematical interpretation and cites the parent analytic framework.
- Publication and expert acceptance remain external social processes and are not implied by a successful build.
