"""
Cazamariposas reports fixes as SMT-level edits, and this module lifts two
types of fixes back to source.

1) `inst_replace prelude_fuel_default`
This type of fix involves "turning off" the prelude_fuel_default axiom using
the #[verifier::fuel_default_off] attribute (which I introduced) and replacing
it with the facts that the solver actually needed using reveal(...) and broadcast use ...

2) `erase/inst_replace/inst_keep internal_…_definition`
This type of fix involves hiding or revealing definition axioms in a single line.

Each reported fix becomes a Candidate carrying the patched text, or a Skip
carrying the reason it could not be lifted.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import List, Optional, Sequence, Tuple

from lifter.lift import (
    Resolved, Unresolved, apply_patch, get_crate_name, get_vir, locate_target,
    resolve, to_crate_relative,
)


@dataclass
class Candidate:
    """
    A Cazamariposas fix lifted to Verus source.
    """

    source_path: Path
    func_name: str
    patched_text: str
    statements: List[str] = field(default_factory=list)
    label: str = ""
    origin_qid: str = ""

    @property
    def change_size(self) -> int:
        """
        How invasive the fix is, as a count of inserted statements.
        """
        return len(self.statements)


@dataclass
class Skip:
    """
    A fix that was not lifted, and why.
    """

    origin_qid: str
    axiom_id: str
    reason: str


# ---------------------------------------------------------------------------
# The `inst_replace prelude_fuel_default` type of fix
#
# Cazamariposas inserts concrete instances for the functions a query 
# actually needs. In source that is `#[verifier::fuel_default_off]` 
# plus one reveal or broadcast use per instance.
# ---------------------------------------------------------------------------

INST_MARKER = '(set-info :comment "[inst] prelude_fuel_defaults'
ERASE_MARKER = '(set-info :comment "[erase] prelude_fuel_defaults")'
FUEL_ID_RE = re.compile(r"fuel%([^\s)]+)")


def mined_fuel_ids(smt2_path: str) -> List[str]:
    """
    The fuel-ids cazamariposas instantiated, read from its patched .smt2.

    They sit between the [inst] and [erase] markers. Raises Unresolved if either
    marker is missing or a line between them carries no fuel-id.
    """
    lines = Path(smt2_path).read_text().splitlines()
    start = next((i for i, line in enumerate(lines) if INST_MARKER in line), None)
    if start is None:
        raise Unresolved(f"{smt2_path}: no [inst] prelude_fuel_defaults block")
    end = next((i for i, line in enumerate(lines[start + 1:], start + 1)
                if ERASE_MARKER in line), None)
    if end is None:
        raise Unresolved(f"{smt2_path}: [inst] block has no closing [erase] marker")

    fuel_ids = []
    for line in lines[start + 1:end]:
        match = FUEL_ID_RE.search(line)
        if not match:
            raise Unresolved(f"{smt2_path}: unparseable [inst] line: {line.strip()}")
        fuel_ids.append(fuel_id_to_path(match.group(1)))
    return fuel_ids


def fuel_id_to_path(fuel_id: str) -> str:
    """
    Changes the `fuel_id` to syntactically match the shape of a Rust path.
    """
    return fuel_id.replace("!", "::", 1).replace(".", "::").rstrip(":")


def prelude_candidate(proj_path: str, smt2_path: str,
                      origin_qid: str = "") -> Candidate:
    """
    Lifts a prelude_fuel_default fix from the SMT query to a Candidate
    If any of the fuel-ids cannot be resolved the whole fix fails and we
    raise Unresolved.
    """
    vir_text = get_vir(proj_path)
    crate = get_crate_name(proj_path)
    mined = mined_fuel_ids(smt2_path)
    if not mined:
        raise Unresolved(f"{smt2_path}: [inst] block names no fuel-ids")

    statements, unresolved = [], []
    for path in mined:
        try:
            found = resolve(path, proj_path, vir_text)
        except Unresolved:
            unresolved.append(path)
            continue
        statements.append(Resolved(to_crate_relative(found.path, crate),
                                   found.mode, found.broadcast).statement())

    if unresolved:
        raise Unresolved(
            f"{smt2_path}: lifted {len(statements)} of {len(mined)} mined "
            f"fuel-ids, and fuel_default_off needs all of them "
            f"(e.g. {unresolved[0]})")

    source_path, near_line, func_name = locate_target(smt2_path, proj_path)
    return Candidate(
        source_path=source_path,
        func_name=func_name,
        patched_text=apply_patch(source_path, func_name, near_line, statements,
                                 fuel_default_off=True),
        statements=statements,
        label="prelude_fuel_defaults (fuel_default_off)",
        origin_qid=origin_qid,
    )


# ---------------------------------------------------------------------------
# The `erase/inst_replace/inst_keep internal_…_definition` type of fix
#
# This type of fix involves hiding or revealing a single definition axiom
# identified by Cazamariposas.
# ---------------------------------------------------------------------------

DEFINITION_SUFFIX_RE = re.compile(
    r"\.(?:_fuel_to_body_definition|_fuel_to_zero_definition|\?_definition)$")
IMPL_ESCAPE_RE = re.compile(r"impl&__(\d+)")
INTERNAL_PREFIX = "internal_"
ACTION_VERB = {"erase": "hide", "inst_replace": "reveal", "inst_keep": "reveal"}


def is_definition_axiom(axiom_id: str) -> bool:
    """
    Whether this axiom fits into the internal_..._definition category.
    """
    return (axiom_id.startswith(INTERNAL_PREFIX)
            and DEFINITION_SUFFIX_RE.search(axiom_id) is not None)


def axiom_to_path(axiom_id: str) -> str:
    """
    Changes the `axiom_id` to syntactically match the shape of a Rust path.
    """
    body = axiom_id[len(INTERNAL_PREFIX):]
    body = body[:DEFINITION_SUFFIX_RE.search(body).start()]
    body = IMPL_ESCAPE_RE.sub(r"impl&%\1", body)
    return fuel_id_to_path(body)


def per_function_candidate(proj_path: str, smt2_path: str, action: str,
                           axiom_id: str, origin_qid: str = "") -> Candidate:
    """
    Lift a function's definition axiom to a hide or a reveal.
    """
    verb = ACTION_VERB[action]
    path = axiom_to_path(axiom_id)
    found = resolve(path, proj_path, get_vir(proj_path))
    if found.mode != "spec":
        raise Unresolved(
            f"{path}: {found.mode}-mode, and {verb}() takes a spec function")

    statement = f"{verb}({to_crate_relative(found.path, get_crate_name(proj_path))});"
    source_path, near_line, func_name = locate_target(smt2_path, proj_path)
    return Candidate(
        source_path=source_path,
        func_name=func_name,
        patched_text=apply_patch(source_path, func_name, near_line, [statement],
                                 allow_proof_wrap=(action != "erase")),
        statements=[statement],
        label=f"{action} {axiom_id}",
        origin_qid=origin_qid,
    )


# ---------------------------------------------------------------------------
# Generating Candidates from a Cazamariposas log
#
# One log covers one unstable query and may report several independent fixes
# for it. We lift each one, then rank them so a caller can pick which single
# patch to write.
# ---------------------------------------------------------------------------

# Cazamariposas prints `    {edit_id}: {action} {axiom} -> {query_path}`.
FIX_LINE_RE = re.compile(r"^ +(\w+): (\w+) (\S+) -> (\S+)$", re.M)
HEADER_RE = re.compile(r"^Found (\d+) fix\(es\):$", re.M)
PRELUDE_FUEL_AXIOM = "prelude_fuel_defaults"


def parse_log(log_text: str) -> List[Tuple[str, str, str, str]]:
    """
    Every (qid, action, axiom_id, smt2_path) a Cazamariposas log reports.

    Raises RuntimeError if the count disagrees with the log's own header.
    """
    fixes = FIX_LINE_RE.findall(log_text)
    header = HEADER_RE.search(log_text)
    if header and int(header.group(1)) != len(fixes):
        raise RuntimeError(f"log reports {header.group(1)} fix(es), parsed {len(fixes)}")
    return fixes


def all_candidates(proj_path: str, log_path: str) -> Tuple[List[Candidate], List[Skip]]:
    """
    Lift every fix in one query's log into a Candidate or a Skip.
    """
    candidates, skips = [], []
    for qid, action, axiom_id, smt2_path in parse_log(Path(log_path).read_text()):
        try:
            candidates.append(
                _lift(proj_path, smt2_path, action, axiom_id, qid))
        except Unresolved as e:
            skips.append(Skip(qid, axiom_id, str(e)))
        except Exception as e:  # a malformed .smt2 or source file skips one fix
            skips.append(Skip(qid, axiom_id, f"{type(e).__name__}: {e}"))
    return candidates, skips


def _lift(proj_path: str, smt2_path: str, action: str, axiom_id: str,
          qid: str) -> Candidate:
    """
    Dispatch the fix to the category that handles it (fuel_default or internal definition), or reject it as out of scope.
    """
    if axiom_id == PRELUDE_FUEL_AXIOM:
        return prelude_candidate(proj_path, smt2_path, qid)
    if not is_definition_axiom(axiom_id):
        raise Unresolved("not a fuel axiom with a source-level equivalent")
    if action not in ACTION_VERB:
        raise Unresolved(f"action {action!r} has no hide/reveal equivalent")
    return per_function_candidate(proj_path, smt2_path, action, axiom_id, qid)


def rank(candidates: Sequence[Candidate]) -> List[Candidate]:
    """
    Rank Candidates least invasive first.
    """
    return sorted(candidates, key=lambda c: c.change_size)


def best(candidates: Sequence[Candidate]) -> Optional[Candidate]:
    """
    The least invasive candidate, or None if there are none.
    """
    return min(candidates, key=lambda c: c.change_size, default=None)
