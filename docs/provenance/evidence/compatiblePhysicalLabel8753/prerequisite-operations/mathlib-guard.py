"""Require the exact named Mathlib prebuilt dependency."""
from pathlib import Path
import json
import subprocess
root = Path.cwd()
manifest = json.loads((root / "lake-manifest.json").read_text())
expected = next(x["rev"] for x in manifest["packages"] if x["name"] == "mathlib")
actual = subprocess.check_output(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], text=True).strip()
assert expected == actual == "c55e6e786f49471c72fbddbec5415808896aec1e"
olean = root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
assert olean.is_file()
print(json.dumps({"named_mathlib_revision": expected, "actual_mathlib_revision": actual, "Mathlib_olean_exists": True}))
