#!/usr/bin/env python3
"""Check the recorded 16-declaration render without Lean or browser execution."""

from pathlib import Path
import hashlib
import json
import re

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[3]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check():
    verification = json.loads((PACKET / "verification.json").read_text())
    for name, digest in verification["source_sha256"].items():
        assert sha(ROOT / name) == digest, name
    for name, digest in json.loads((PACKET / "packet-sha256.json").read_text()).items():
        assert sha(ROOT / name) == digest, name
    commands = json.loads((PACKET / "commands.json").read_text())
    assert all(code == 0 for code in commands["final_exit_codes"].values())
    for record in commands["normalization"]:
        assert sha(ROOT / record["destination"]) == record["normalized_sha256"]

    declarations = []
    guarded = []
    for module in ("DoubledSystemGap", "PositiveGapUniqueness"):
        source = (ROOT / f"QICLean/Analysis/{module}.lean").read_text()
        tests = (ROOT / f"QICLeanTest/{module}.lean").read_text()
        declarations.extend(re.findall(r"^Downstream declaration: (\S+)$", source, re.M))
        names = re.findall(r"^#print axioms (\S+)$", tests, re.M)
        assert len(names) == len(re.findall(r"^#guard_msgs", tests, re.M))
        guarded.extend(names)
    leaf = (ROOT / "blueprint/src/chapter/ch12_entropy_doubled_system_gap.tex").read_text()
    tags = [
        name.strip()
        for group in re.findall(r"\\lean\{([^}]+)\}", leaf, re.S)
        for name in group.split(",")
    ]
    assert len(declarations) == len(tags) == len(guarded) == 16
    assert set(declarations) == set(tags) == set(guarded) == set(verification["declarations"])
    assert len(re.findall(r"\\leanok\b", leaf)) == 11
    assert verification["missing_internal_anchors"] == []
    assert verification["new_declaration_links"] == 16
    assert verification["reused_declaration_links"] == 43
    assert verification["diagram"]["pdf_and_standalone_semantics_agree"] is True
    print("PASS: 16 source notices, blueprint links, guards, and recorded focused-render hashes")


if __name__ == "__main__":
    check()
