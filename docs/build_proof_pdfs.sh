#!/usr/bin/env bash
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build="$repo/docs/build"

# TeX engines honor these variables for creation dates and other time-dependent
# metadata.  A fixed epoch makes a rebuild depend on the sources, not wall time.
export SOURCE_DATE_EPOCH=0
export FORCE_SOURCE_DATE=1
export TZ=UTC

mkdir -p "$build"

for _pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$build" "$repo/docs/hahn_kaplansky_proof.tex"
  uplatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$build" "$repo/docs/hahn_kaplansky_proof_ja.tex"
done
dvipdfmx -q -o "$build/hahn_kaplansky_proof_ja.pdf" \
  "$build/hahn_kaplansky_proof_ja.dvi"

if rg -n 'Warning|Overfull|Underfull|undefined|Error|Fatal' \
  "$build/hahn_kaplansky_proof.log" \
  "$build/hahn_kaplansky_proof_ja.log"; then
  printf 'PDF build emitted warnings or errors.\n' >&2
  exit 1
fi
printf 'PDF build completed without warnings.\n'

update_pdf() {
  local generated="$1"
  local committed="$2"
  if [[ -f "$committed" ]] && cmp -s "$generated" "$committed"; then
    printf 'unchanged: %s\n' "${committed#"$repo/"}"
  else
    cp "$generated" "$committed"
    printf 'updated: %s\n' "${committed#"$repo/"}"
  fi
}

update_pdf "$build/hahn_kaplansky_proof.pdf" \
  "$repo/docs/hahn_kaplansky_proof.pdf"
update_pdf "$build/hahn_kaplansky_proof_ja.pdf" \
  "$repo/docs/hahn_kaplansky_proof_ja.pdf"
