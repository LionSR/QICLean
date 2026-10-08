from pathlib import Path
import json, subprocess
root = Path.cwd()
manifest = json.loads((root / "lake-manifest.json").read_text())
mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
package = root / ".lake/packages/mathlib"
revision = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
assert revision == mathlib["rev"]
assert (package / ".lake/build/lib/lean/Mathlib.olean").is_file()
assert not subprocess.check_output(["git", "-C", str(package), "status", "--porcelain"], text=True)
print("PREBUILT_GUARD_PASS", revision)
