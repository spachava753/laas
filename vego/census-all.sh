#!/bin/sh
# Run the census of vego over its four corpora, like for like with F41's
# run (vego/ROADMAP.md, The census): the modules of vego/census.list, laas
# without its vego package (census-laas.list), the trial (census-trial.list,
# from the checkout TRIAL names), and the standard library in seven groups
# (census-std.list), one corpus after another, each through vego/census.sh,
# one laas at a time.
#
# Usage: TRIAL=DIR vego/census-all.sh LAAS VEGOCENSUS OUTDIR
#
# It leaves one census file per corpus, OUTDIR/modules.jsonl,
# OUTDIR/laas.jsonl, OUTDIR/trial.jsonl, and OUTDIR/std.jsonl, as F41's run
# did; then go run ./cmd/vegocensus summary laas=OUTDIR/laas.jsonl
# trial=OUTDIR/trial.jsonl std=OUTDIR/std.jsonl modules=OUTDIR/modules.jsonl.
# Only one census runs on the machine at a time: the driver stops if
# another census.sh runs.
set -u
laas=$1 vegocensus=$2 out=$3
here=$(cd "$(dirname "$0")" && pwd)
if pgrep -f 'census\.sh' > /dev/null; then
	echo "census-all.sh: another census runs; wait for it to end" >&2
	exit 1
fi
: "${TRIAL:?set TRIAL to the directory of the trial}"
mkdir -p "$out/stdmod"
printf 'module stdrun\n\ngo 1.27\n' > "$out/stdmod/go.mod"
printf 'package stdrun\n' > "$out/stdmod/x.go"
for c in modules laas trial std; do
	case $c in
	modules) list=$here/census.list ;;
	*) list=$here/census-$c.list ;;
	esac
	echo "start $c $(date +%T)" >> "$out/progress"
	if [ "$c" = std ]; then
		STD_SKIP='^(cmd|runtime|internal|vendor|builtin)(/|$)|/internal(/|$)|^syscall(/|$)|^unsafe$|/testdata(/|$)' CENSUS_TIMEOUT=1800 \
			CENSUS_STDMOD="$out/stdmod" CENSUS_TRIAL="$TRIAL" sh "$here/census.sh" "$laas" "$vegocensus" "$list" "$out/$c" > "$out/$c.out" 2>&1
	else
		CENSUS_STDMOD="$out/stdmod" CENSUS_TRIAL="$TRIAL" sh "$here/census.sh" "$laas" "$vegocensus" "$list" "$out/$c" > "$out/$c.out" 2>&1
	fi
	echo "end $c $(date +%T)" >> "$out/progress"
done
cat "$out"/modules/*.jsonl > "$out/modules.jsonl"
cp "$out/laas/laas.jsonl" "$out/laas.jsonl"
cp "$out/trial/trial.jsonl" "$out/trial.jsonl"
cp "$out/std/std-all.jsonl" "$out/std.jsonl"
