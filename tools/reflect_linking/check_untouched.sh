#!/bin/bash
# check_untouched.sh <repository root> [ref ...]
# Lists every path of the bundle that (a) is tracked on one of the given refs (default: HEAD), or
# (b) already exists in the working tree and differs from the bundle's copy.  Run it from the directory
# that holds reflect_families_bundle.tar.zst, BEFORE or AFTER unpacking.  No output lines after the
# header means that the bundle adds files only.
set -euo pipefail
REPO="${1:?repository root}"; shift || true
REFS=("$@"); [ ${#REFS[@]} -eq 0 ] && REFS=(HEAD)
B="${BUNDLE:-reflect_families_bundle.tar.zst}"
[ -f "$B" ] || { echo "bundle $B not found (set BUNDLE=...)" >&2; exit 2; }
T=$(mktemp -d); zstd -dc "$B" | tar -xf - -C "$T"
n=0; hits=0
echo "checking $(cd "$T" && find . -type f | wc -l | tr -d ' ') bundle paths against: ${REFS[*]} and the working tree of $REPO"
while IFS= read -r f; do
  f="${f#./}"; n=$((n+1))
  for r in "${REFS[@]}"; do
    if git -C "$REPO" cat-file -e "$r:$f" 2>/dev/null; then echo "TRACKED on $r: $f"; hits=$((hits+1)); fi
  done
  if [ -e "$REPO/$f" ] && ! cmp -s "$REPO/$f" "$T/$f"; then echo "EXISTS AND DIFFERS in working tree: $f"; hits=$((hits+1)); fi
done < <(cd "$T" && find . -type f | sort)
echo "paths=$n hits=$hits"
[ "$hits" -eq 0 ]
