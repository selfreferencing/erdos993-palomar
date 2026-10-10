#!/bin/bash
# consumer_test.sh FAMILY   (run in the repository root, on a tree where the family's Reflect modules exist)
#
# Compiles every consumer of the family against the reflective Program, WITHOUT touching an existing file:
# for each public root it writes two copies under Erdos993Lean/F4U/Light/Reflect/ConsumerTest/<FAMILY>/
#   CN_<root>.lean  = Linking/CheckedNumerators/<root>.lean with the import of the family Program replaced by
#                     Erdos993Lean.F4U.Light.Reflect.<FAMILY>.Program and the family namespace opened as
#                     F4U.Light.Short3.<FAMILY>_P10 (the shape the Short3 wiring gives these files)
#   AP_<root>.lean  = Construction/ActualPositivity/<root>.lean importing that copy, with the same extra `open`
# and builds them all.  The copies keep the original declaration names, so never import them next to the originals.
set -u
F="$1"; T=Erdos993Lean/F4U/Light/Reflect/ConsumerTest/$F; mkdir -p "$T"
roots=$(grep -o "^abbrev [A-Za-z0-9_]*_pair := n" Erdos993Lean/F4U/Light/Reflect/$F/Roots.lean | sed 's/^abbrev //; s/_pair := n$//')
n=0; bad=0
for r in $roots; do
  cn=Erdos993Lean/F4U/Light/Linking/CheckedNumerators/$r.lean; ap=Erdos993Lean/F4U/Light/Construction/ActualPositivity/$r.lean
  sed -e "s|^public import Erdos993Lean\.F4U\.Light\.Linking\.Generated\.$F\.Program\$|public import Erdos993Lean.F4U.Light.Reflect.$F.Program|" \
      -e "s|^open F4U\.Light\.Linking\.Generated\.$F\$|open F4U.Light.Short3.${F}_P10|" "$cn" > "$T/CN_$r.lean"
  sed -e "s|^public import Erdos993Lean\.F4U\.Light\.Linking\.CheckedNumerators\.$r\$|public import Erdos993Lean.F4U.Light.Reflect.ConsumerTest.$F.CN_$r|" \
      -e "s|^open F4U\.Light\.Linking\.Generated\.$F\$|open F4U.Light.Linking.Generated.$F\nopen F4U.Light.Short3.${F}_P10|" "$ap" > "$T/AP_$r.lean"
  grep -q "^public import Erdos993Lean.F4U.Light.Reflect.$F.Program$" "$T/CN_$r.lean" && grep -q "^open F4U.Light.Short3.${F}_P10$" "$T/CN_$r.lean" \
    && grep -q "ConsumerTest.$F.CN_$r$" "$T/AP_$r.lean" && grep -q "^open F4U.Light.Short3.${F}_P10$" "$T/AP_$r.lean" || bad=$((bad+1))
  [ "$(diff "$cn" "$T/CN_$r.lean" | grep -c '^[<>]')" = 4 ] || bad=$((bad+1))
  [ "$(diff "$ap" "$T/AP_$r.lean" | grep -c '^[<>]')" = 3 ] || bad=$((bad+1))
  n=$((n+1))
done
{ echo module; for r in $roots; do echo "public import Erdos993Lean.F4U.Light.Reflect.ConsumerTest.$F.AP_$r"; done; } > "$T/All.lean"
echo "consumer_test $F: roots=$n rewrite_problems=$bad"
s=$(date +%s)
lake build Erdos993Lean.F4U.Light.Reflect.ConsumerTest.$F.All > "$T/build.log" 2>&1; rc=$?
echo "consumer_test $F: build rc=$rc wall_s=$(( $(date +%s) - s )) built=$(grep -c 'Built Erdos993Lean.F4U.Light.Reflect.ConsumerTest' "$T/build.log") errors=$(grep -c -E '^error|: error' "$T/build.log") actual_positive_axiom_lines=$(grep -c "actual_positive' depends on axioms" "$T/build.log")"
echo "consumer_test $F: axiom lists printed for actual_positive (count, list):"
tr '\n' ' ' < "$T/build.log" | grep -o "actual_positive' depends on axioms: \[[^]]*\]" | sed -E "s/ +/ /g; s/.*axioms: //" | sort | uniq -c
tail -n 1 "$T/build.log" | cut -c1-120
