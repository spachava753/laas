#!/bin/sh
# Run a census of vego over a list of modules, one laas process at a time.
#
# Usage: vego/census.sh LAAS VEGOCENSUS LIST OUTDIR
#
# LAAS is a laas binary and VEGOCENSUS a vegocensus binary (cmd/vegocensus).
# Each line of LIST is "NAME DIR SCOPE [PATTERNS...]": the corpus or module
# NAME, its directory, the module path the census looks at (std for the
# standard library), and the package patterns, ./... by default. Lines that
# start with # are comments. A directory in the module cache is copied
# under OUTDIR first, since the cache is read-only. A module with no
# vego-trusted.yaml of its own is looked at with OUTDIR/declared.yaml,
# which declares only the memory and the inputs of the guide.
#
# Each run is one laas process in a scope of 12G with 4G of swap, bounded
# at 600 seconds, with GOMAXPROCS=4. OUTDIR/NAME.jsonl gets the census and
# OUTDIR/NAME.log what laas printed; a run that failed or timed out is
# listed in OUTDIR/failed.txt, and the functions that left no line, as of a
# package that did not load or whose analysis failed, are added by
# vegocensus notloaded as package:not-loaded and their packages listed in
# OUTDIR/missing.txt. Groups of the standard library (SCOPE std) are held
# together at the end against GOROOT/src, without the packages that the
# expression STD_SKIP matches.
set -u
laas=$1 vegocensus=$2 list=$3 out=$4
mkdir -p "$out/src"
cat > "$out/declared.yaml" <<'YAML'
version: 1
sizes:
  memory: 256GB
  reason: >-
    The census looks at code as a project that declares the memory of the guide.
inputs:
  bytes: 1TB
  reason: >-
    The census looks at code as a project that declares the inputs of the guide.
YAML
: > "$out/failed.txt"
cache=$(go env GOMODCACHE)
# notloaded adds a line of package:not-loaded for every function with a body
# that the census file has none for, and lists in OUTDIR/missing.txt each
# package of them with what laas printed about it.
notloaded() {
	"$vegocensus" notloaded -module "$1" -dir "$2" -have "$3" -skip "$5" > "$out/$4.notloaded"
	cat "$out/$4.notloaded" >> "$3"
	grep -o '"package":"[^"]*"' "$out/$4.notloaded" | sort -u | cut -d'"' -f4 | while read -r pkg; do
		echo "$4: $pkg: $(grep -hF "$pkg" "$out"/*.log 2>/dev/null | head -n 2 | tr '\n' ' ')" >> "$out/missing.txt"
	done
}
: > "$out/missing.txt"
rm -f "$out/std-all.jsonl"
grep -v '^#' "$list" | while read -r name dir scope patterns; do
	[ -n "$name" ] || continue
	patterns=${patterns:-./...}
	case $dir in
	"$cache"/*)
		rm -rf "$out/src/$name"
		cp -r "$dir" "$out/src/$name"
		chmod -R u+w "$out/src/$name"
		dir=$out/src/$name
		;;
	esac
	trusted=
	[ -f "$dir/vego-trusted.yaml" ] || trusted=-vego.trusted=$out/declared.yaml
	rm -f "$out/$name.jsonl"
	start=$(date +%s)
	(cd "$dir" && systemd-run --user --scope --quiet -p MemoryMax=12G -p MemorySwapMax=4G -- \
		env GOMAXPROCS=4 GOFLAGS="-mod=mod -buildvcs=false" GOPROXY=off GOSUMDB=off GOTOOLCHAIN=local GOWORK=off \
		timeout 600 "$laas" -vego -test=false -vego.census="$out/$name.jsonl" -vego.census-scope="$scope" $trusted $patterns) \
		> "$out/$name.log" 2>&1
	status=$?
	echo "$name: exit $status, $(($(date +%s) - start)) s" >> "$out/times.txt"
	if [ $status -ne 0 ]; then
		echo "$name: exit $status: $(grep -m1 -v '^$' "$out/$name.log")" >> "$out/failed.txt"
	fi
	if [ "$scope" = std ]; then
		cat "$out/$name.jsonl" >> "$out/std-all.jsonl" 2>/dev/null
		continue
	fi
	notloaded "$scope" "$dir" "$out/$name.jsonl" "$name" ""
done
# The groups of the standard library are held together against GOROOT/src,
# leaving out the packages STD_SKIP matches, which were not asked for.
if [ -f "$out/std-all.jsonl" ]; then
	notloaded std "$(go env GOROOT)/src" "$out/std-all.jsonl" std "${STD_SKIP:-^$}"
fi
