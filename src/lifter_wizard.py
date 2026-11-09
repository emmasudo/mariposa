#!/usr/bin/env python3

"""
Lifter wizard operates on the single-query level. The input is a
Cazamariposas log, whose fixes are SMT-level edits, and the output is a Verus
source file carrying the equivalent source-level statements.
"""

import argparse
import sys
from pathlib import Path

from lifter.fixes import (
    all_candidates, best, rank,
)

def setup_lift(subparsers):
    p = subparsers.add_parser(
        "lift",
        help="lift every fuel fix in a cazamariposas log, writing the least invasive one",
    )
    p.add_argument("project_path", help="path to the Verus project the log came from")
    p.add_argument("caza_log_path", help="path to the Cazamariposas log")
    p.add_argument("output_path", help="path to the fixed .rs file")


def run_lift(args):
    """
    Report every fix the log holds, then write the one we would apply.

    A fix that could not be lifted in full is printed as a skip; it never
    becomes a candidate, so it cannot be the one written.
    """
    candidates, skips = all_candidates(args.project_path, args.caza_log_path)
    for skip in skips:
        print(f"skipped {skip.origin_qid} ({skip.axiom_id}): {skip.reason}")
    if not candidates:
        print("no fix candidates in this log", file=sys.stderr)
        return 1

    print(f"\n{len(candidates)} candidate(s):")
    for candidate in rank(candidates):
        print(f"\n  [{candidate.change_size} stmt(s)] {candidate.label}")
        print(f"  target: {candidate.func_name} in {candidate.source_path}")
        for statement in candidate.statements:
            print(f"      {statement}")

    winner = best(candidates)
    Path(args.output_path).write_text(winner.patched_text)
    print(f"\npicked: {winner.label} ({winner.change_size} statement(s))")
    print(f"wrote {args.output_path}; the original source is untouched")
    return 0

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    subparsers = parser.add_subparsers(
        dest="sub_command", help="the sub-command to run"
    )

    setup_lift(subparsers)

    args = parser.parse_args()

    if args.sub_command == "lift":
        sys.exit(run_lift(args))
    else:
        parser.print_help()
        sys.exit(1)
