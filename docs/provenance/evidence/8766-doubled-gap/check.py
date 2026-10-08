#!/usr/bin/env python3
"""Check recorded doubled-gap evidence without invoking Lean or Lake."""

from pathlib import Path
import hashlib
import json
import re
import subprocess

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[3]


def evidence_bytes(path):
    """Use the attested historical leaf for the original 13-link render."""
    frozen = read_json(PACKET / "frozen-blueprint.json")
    if path == ROOT / frozen["path"]:
        return subprocess.check_output(
            ["git", "show", f'{frozen["revision"]}:{frozen["path"]}'], cwd=ROOT
        )
    return path.read_bytes()


def sha(path):
    return hashlib.sha256(evidence_bytes(path)).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def check():
    recorded = read_json(PACKET / "verification.json")
    for name, digest in recorded["source_sha256"].items():
        assert sha(ROOT / name) == digest, name
    for item in recorded["normalization"]:
        assert sha(ROOT / item["destination"]) == item["normalized_sha256"], item
    for name, digest in read_json(PACKET / "packet-sha256.json").items():
        assert sha(ROOT / name) == digest, name

    source = (ROOT / "QICLean/Analysis/DoubledSystemGap.lean").read_text()
    tests = (ROOT / "QICLeanTest/DoubledSystemGap.lean").read_text()
    raw = (PACKET / "drivers/DoubledSystemGapRawAxioms.lean").read_text()
    leaf = evidence_bytes(
        ROOT / "blueprint/src/chapter/ch12_entropy_doubled_system_gap.tex"
    ).decode()
    pairs = re.findall(
        r"^Provenance-ID: (\S+)\nDownstream declaration: (\S+)", source, re.M
    )
    declarations = set(recorded["declarations"])
    assert len(pairs) == len(declarations) == 13
    assert {decl for _, decl in pairs} == declarations
    assert set(re.findall(r"^#print axioms (\S+)$", raw, re.M)) == declarations
    assert set(re.findall(r"^#print axioms (\S+)$", tests, re.M)) == declarations
    assert len(re.findall(r"^#guard_msgs", tests, re.M)) == 13
    tags = [
        name.strip()
        for group in re.findall(r"\\lean\{([^}]+)\}", leaf, re.S)
        for name in group.split(",")
    ]
    assert len(tags) == 13 and set(tags) == declarations
    assert not re.search(r"\b(?:sorry|admit|native_decide|unsafeCast)\b", source)

    ledger = read_json(ROOT / "docs/provenance/openai-math.d/doubled8766.json")
    binding = read_json(PACKET / "public-checkpoint-attestation.json")
    public_tree = subprocess.check_output(
        ["git", "rev-parse", binding["public_revision"] + "^{tree}"], cwd=ROOT, text=True
    ).strip()
    assert public_tree == binding["public_tree"] == binding["local_checkpoint_tree"]
    historical_ledger = read_json(PACKET / "historical-ledger-57bf.json")
    assert all(
        e["verification"]["revision"] == recorded["integrated_revision"]
        for e in historical_ledger["entries"]
    )
    for name, digest in binding["source_sha256"].items():
        public_bytes = subprocess.check_output(
            ["git", "show", f'{binding["public_revision"]}:{name}'], cwd=ROOT
        )
        assert hashlib.sha256(public_bytes).hexdigest() == digest, name
    entries = ledger["entries"]
    assert len(entries) == 13
    assert {(x["id"], x["downstream"]["declaration"]) for x in entries} == set(pairs)
    for entry in entries:
        assert entry["no_upstream_proof_text_reused"] is True
        assert entry["verification"]["revision"] == binding["public_revision"]
        for run in entry["verification"]["commands"]:
            assert run["exit_code"] == 0
            assert sha(ROOT / run["log"]) == run["sha256"]

    historical = read_json(PACKET / "runs/doubled-gap-strict-first.json")
    final = read_json(PACKET / "runs/doubled-gap-tests-b4ac.json")
    integrated = read_json(PACKET / "runs/doubled-integrated-57bf.json")
    assert [r["exit_code"] for r in historical] == [0, 1, 0]
    assert final[0]["exit_code"] == 0
    assert final[0]["sha256"] == sha(ROOT / final[0]["file"])
    assert historical[1]["sha256"] != final[0]["sha256"]
    assert all(r["exit_code"] == 0 for r in integrated)
    assert all(r["head"] == recorded["integrated_revision"] for r in integrated)

    axiom_pattern = r"'([^']+)' depends on axioms:\s*\[([^\]]+)\]"
    for name in (
        "doubled-gap-8766-raw-audit.lean-doubled-gap-strict-first.log",
        "doubled-integrated-57bf-3.log",
    ):
        axioms = re.findall(axiom_pattern, (PACKET / "logs" / name).read_text())
        assert len(axioms) == 13 and {decl for decl, _ in axioms} == declarations
        for decl, values in axioms:
            assert {x.strip() for x in values.split(",")} == set(recorded["standard_axioms"]), decl

    render = read_json(PACKET / "render/verification.json")
    for name, digest in render["source_sha256"].items():
        assert sha(ROOT / name) == digest, name
    assert set(render["declarations"]) == declarations
    assert render["new_declaration_links"] == 13
    assert render["missing_internal_anchors"] == []
    assert render["diagram"]["pdf_and_standalone_semantics_agree"] is True
    print("PASS: 13 source notices, frozen blueprint links, guards, raw axioms, ledger entries, and evidence hashes")


if __name__ == "__main__":
    check()
