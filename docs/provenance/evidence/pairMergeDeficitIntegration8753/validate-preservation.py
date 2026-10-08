"""Check inherited bytes, frozen proofs and the narrow book inclusion."""
from pathlib import Path
import hashlib
import json
import subprocess
root=Path.cwd()
folder=Path(__file__).resolve().parent
sha=lambda data:hashlib.sha256(data).hexdigest()
leaf=root/"docs/provenance/evidence/pairMergeDeficit8753"
parent=json.loads((leaf/"parent-before.json").read_text())
changed={p for p,h in parent["files_sha256"].items() if sha((root/p).read_bytes())!=h}
assert changed=={"QICLean/Representation.lean","blueprint/src/chapter/ch13_schur_labels.tex","docs/tactic_patterns.md"},changed
get=lambda p:subprocess.check_output(["git","show",parent["revision"]+":"+p])
assert (root/"QICLean/Representation.lean").read_bytes().replace(b"import QICLean.Representation.PairMergeDeficit\n",b"")==get("QICLean/Representation.lean")
assert (root/"blueprint/src/chapter/ch13_schur_labels.tex").read_bytes().replace(b"\\input{fragment/pair_merge_deficit}\n",b"")==get("blueprint/src/chapter/ch13_schur_labels.tex")
assert (root/"docs/tactic_patterns.md").read_bytes().startswith(get("docs/tactic_patterns.md"))
for p,h in json.loads((leaf/"manifest.json").read_text())["artifacts_sha256"].items():
 assert sha((root/p).read_bytes())==h,p
for p in ["QICLean/Representation/PairMergeDeficit.lean","docs/openai-area-law-pair-merge-deficit.md","docs/tactic_patterns.md"]:
 assert (root/p).read_bytes()==subprocess.check_output(["git","show","f028f8c6:"+p]),p
assert subprocess.check_output(["git","rev-parse","feat/area-law-pair-merge-moment"],text=True).strip()==parent["revision"]
print("All1912 inherited paths preserved except exact import/input and ledger append; all24 leaf artifacts and frozen source bytes unchanged; published paired branch preserved.")
