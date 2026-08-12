#!/usr/bin/env python3
"""Extract the sorted union of Lean `#print axioms` blocks.

Lean may colorize the declaration name and may wrap the bracketed axiom list
across lines.  The old line-oriented sed expression silently produced an
empty file in either case, so this parser first removes ANSI control sequences
and then matches each complete bracketed block.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ANSI_ESCAPE = re.compile(r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))")
AXIOM_BLOCK = re.compile(r"depends on axioms:\s*\[(.*?)\]", re.DOTALL)


def extract_axioms(text: str) -> list[str]:
    clean = ANSI_ESCAPE.sub("", text)
    blocks = AXIOM_BLOCK.findall(clean)
    if not blocks:
        raise ValueError("no complete `depends on axioms: [...]` block found")
    return sorted({
        token.strip()
        for block in blocks
        for token in block.split(",")
        if token.strip()
    })


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    axioms = extract_axioms(args.input.read_text(encoding="utf-8", errors="replace"))
    payload = "".join(f"{axiom}\n" for axiom in axioms)
    args.output.write_text(payload, encoding="utf-8")
    print(f"parsed {len(axioms)} distinct axioms from {args.input}")


if __name__ == "__main__":
    main()
