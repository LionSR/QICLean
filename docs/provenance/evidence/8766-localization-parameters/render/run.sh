#!/usr/bin/env bash
# Use an existing blueprint Python environment and configured TeX search tree.
# TENKZ_ROOT must point to the revision pinned by the source's tenkz.toml.
set -euo pipefail
if [ "$#" -ne 2 ]; then
  printf 'Usage: %s SOURCE_ROOT NEW_EXTERNAL_RENDER_DIRECTORY\n' "$0" >&2
  exit 2
fi
source_root=$(realpath "$1")
render_dir=$(realpath -m "$2")
validation_dir="$source_root/docs/provenance/evidence/8766-localization-parameters/render"
export PYTHONDONTWRITEBYTECODE=1
export XDG_CACHE_HOME="$render_dir/cache"
python "$validation_dir/prepare.py" --source-root "$source_root" --output "$render_dir"
(
  cd "$render_dir/blueprint/src"
  latexmk -xelatex -interaction=nonstopmode -halt-on-error print.tex > ../../pdf-build.log 2>&1
  cp print.bbl web.bbl
  plastex -c plastex.cfg web.tex > ../../web-build.log 2>&1
)
(
  cd "$render_dir"
  python scripts/tenkz_blueprint_sweep.py --src blueprint/src --allow-empty > tenkz-sweep.log 2>&1
)
python "$validation_dir/verify.py" --source-root "$source_root" --render "$render_dir" > "$render_dir/verify-final.log" 2>&1
printf 'Verified focused render: %s/verification.json\n' "$render_dir"
