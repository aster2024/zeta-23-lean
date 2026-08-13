# Raw evidence used by the companion paper

These files are copied without modification from
`work/zeta_two_thirds_audit_20260811`.

- `wider_four_point_rational_ledger.py` and its output verify the six-root localization constants, all 216 ordered root-index budgets, the local energy, and the endpoint increment.
- `wider_fixed_interface_ceiling_ledger.py` and its output verify the active strict-localization ceiling and exclude the immediately larger unit fraction inside the frozen interface.
- `receipt.json` records the pinned public GitHub Actions build for source commit `d368cc49d689576c81d7e4df0c135057d2462a27`.
- `sources/zeta-23-lean/` contains the five exact Lean source snapshots read by
  `wider_four_point_rational_ledger.py`.  They make the ledger independently
  replayable inside this archive instead of relying on the original research
  workspace.

The corresponding Lean sources live in the public repository
`https://github.com/aster2024/zeta-23-lean` on branch
`codex/wider-strict-improvement-79828975`.

For a byte comparison with the recorded output, run:

```bash
python3 wider_four_point_rational_ledger.py --verify-frozen-output
python3 wider_fixed_interface_ceiling_ledger.py --verify-frozen-output
```
