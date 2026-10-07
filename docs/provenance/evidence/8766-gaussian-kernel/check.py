#!/usr/bin/env python3
"""Check Gaussian-kernel evidence without Lean, network access, or external writes."""
import hashlib
import json
from pathlib import Path
import re
import sys

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[3]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


index = load(PACKET / "verification.json")
ledger = load(ROOT / "docs/provenance/openai-math.d/gaussiankernel8766.json")
for path in PACKET.rglob("*.json"):
    load(path)
for item in index["normalization"]["original_to_normalized"]:
    path = PACKET / item["retained"]
    require(digest(path) == item["normalized_sha256"], f"Changed retained input: {path}")
    require(path.stat().st_size == item["normalized_bytes"], "Retained input size differs")
for item in index["source_files"]:
    path = ROOT / item["path"]
    data = path.read_bytes()
    require(digest(path) == item["sha256"], f"Changed checked source: {path}")
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    require(blob == item["git_blob"], "Source Git blob differs")
    require(len(data.splitlines()) == item["lines"], "Source line count differs")

source = (ROOT / index["source_files"][0]["path"]).read_text()
test = (ROOT / index["source_files"][1]["path"]).read_text()
driver = (ROOT / index["source_files"][2]["path"]).read_text()
pairs = re.findall(r"^Provenance-ID: (\S+)\nDownstream declaration: (\S+)$", source, re.M)
names = [name for _, name in pairs]
require(len(pairs) == len(ledger["entries"]) == 15, "Expected fifteen declarations and rows")
require(len(set(names)) == 15, "Duplicate public declaration")
require(names == ["GaussianFilter." + name for name in
                  re.findall(r"^(?:noncomputable def|theorem) (\w+)", source, re.M)],
        "Public declaration coverage differs")
require(names == re.findall(r"^#guard_msgs[^\n]*\n#print axioms (\S+)$", test, re.M),
        "Guarded axiom coverage differs")
require(names == re.findall(r"^#print axioms (\S+)$", driver, re.M), "Raw coverage differs")
require(len(re.findall(r"^example\b", test, re.M)) == index["test_examples"] == 9,
        "Consumer count differs")
require(not re.search(r"\b(sorry|admit|native_decide|unsafeCast|unsafeCoerce)\b", source),
        "Proof integrity blocker in production")
require(not re.search(r"^\s*axiom\b|set_option\s+(?:maxHeartbeats|maxRecDepth|linter\.)",
                      source, re.M), "Unexpected axiom, budget increase, or linter option")

chosen_commands = []
for selected in index["selected_successful_runs"]:
    row = load(PACKET / selected["record"])[selected["row"]]
    require(row["exit_code"] == 0, "Selected run failed")
    require((ROOT / row["log"]).is_file(), "Selected output is missing")
    if row["sha256"]:
        require(digest(ROOT / row["file"]) == row["sha256"], "Checked source hash differs")
    if selected["kind"] != "native-target":
        for option in ["-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                       "-Dlinter.mathlibStandardSet=true", "-DwarningAsError=true"]:
            require(option in row["command"], f"Missing strict option: {option}")
    chosen_commands.append({"kind": "axioms" if selected["kind"] == "strict-raw-axioms"
                            else "build", "command": " ".join(row["command"]),
                            "exit_code": 0, "log": row["log"],
                            "sha256": digest(ROOT / row["log"])})

failed = []
for record in sorted((PACKET / "history/runs").glob("*.json")):
    for ordinal, row in enumerate(load(record)):
        require((ROOT / row["log"]).is_file(), "Historical output is missing")
        if row["exit_code"]:
            failed.append((f"history/runs/{record.name}", ordinal, row["head"], row["exit_code"]))
require(failed == [(r["record"], r["row"], r["head"], r["exit_code"])
                  for r in index["historical_failed_runs"]], "Historical failures differ")
require(len(failed) == 2, "Expected two preserved failed invocations")

for entry, pair in zip(ledger["entries"], pairs):
    require((entry["id"], entry["downstream"]["declaration"]) == pair, "Ledger identity differs")
    require(entry["reuse_kind"] == "original" and entry["upstream"] is None and
            entry["no_upstream_proof_text_reused"], "OpenAI proof-text category differs")
    require(entry["verification"]["revision"] == index["verified_source_revision"],
            "Verification revision differs")
    require(entry["verification"]["commands"] == chosen_commands, "Ledger commands differ")

raw = load(PACKET / "runs/gaussian-kernel-b45b.json")[3]
output = (ROOT / raw["log"]).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
require([name for name, _ in reports] == names, "Raw reports differ")
for name, axioms in reports:
    actual = [a.strip() for a in axioms.split(",")]
    require(actual == index["axioms"][name] == ["propext", "Classical.choice", "Quot.sound"],
            "Unexpected axiom")
require(output.count("[linter.hashCommand]") == 15, "Raw informational diagnostics differ")
reuse = load(PACKET / "library-reuse.json")
require([item["downstream"] for item in reuse["declarations"]] == names,
        "Library reuse coverage differs")
require(not reuse["openai_lean_proof_text_reused"], "Unexpected upstream proof-text reuse")
require(reuse["mathlib"]["commit"] == "c55e6e786f49471c72fbddbec5415808896aec1e",
        "Mathlib revision differs")
for path in list(PACKET.rglob("*")) + [ROOT / "docs/provenance/openai-math.d/gaussiankernel8766.json"]:
    if path.is_file():
        require(not re.search(r"/(?:workspace/scratch|home/agent|root)/", path.read_text()),
                f"Private executor path retained: {path}")

schema_validated = False
if len(sys.argv) == 2:
    import jsonschema
    schema = Path(sys.argv[1])
    require(digest(schema) == index["schema_check"]["schema_sha256"], "Schema differs")
    jsonschema.validate(ledger, load(schema))
    schema_validated = True
require(len(sys.argv) <= 2, "Usage: check.py [provenance-schema.json]")
print(json.dumps({"status": "passed", "public_declarations": 15, "consumer_examples": 9,
                  "guarded_reports": 15, "raw_reports": 15, "historical_failures": 2,
                  "verified_source_revision": index["verified_source_revision"],
                  "schema_validated": schema_validated,
                  "scope": "Retained evidence and file identities; no Lean or CI execution."},
                 indent=2))
