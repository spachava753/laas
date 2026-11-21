#!/bin/sh
# repeat.sh runs laas on one module several times, two runs at a time, and
# checks that every run printed the same thing as the first: the same
# diagnostics, the same -vego.cost figures, and the same exit status.
#
# Usage: vego/repeat.sh [-filling] LAAS DIR RUNS [laas arguments...]
#
#   LAAS  a laas binary
#   DIR   the module to run it in
#   RUNS  how many runs, 2 to 50
#
# for example
#
#   vego/repeat.sh /tmp/laas ~/dev/vego-trial 20 -vego -vego.cost -test=false -exclude-packages=findings ./...
#
# The whole check runs in one systemd scope limited to 12G of memory and 4G
# of swap, which it starts itself, and each run is bounded at 30 minutes.
# Two runs at a time is two verifiers, each with up to four Z3 processes:
# that is the load under which a run once differed from the next.
#
# What may differ between runs and is left out of the comparison:
#
#   - the seconds of a -vego.cost line, which follow the machine;
#   - with -filling, which is for runs that share a cache directory
#     (-vego.cache) that starts empty or is being filled, whether an answer
#     came from that directory or from Z3, since that depends on which run
#     wrote it first: the ", N answered from the answer cache on disk" of a
#     -vego.cost line, the line "vego: N of the M answers of Z3 for P came
#     from the answer cache in DIR", and the paragraph of the trust report
#     that begins "Answers of Z3 read from the answer cache:".
#
# Two other things can make runs differ by design, and then the difference
# shows: a problem that runs past the wall limit, which the report names,
# and a wrong answer in a cache directory, which a sample drawn anew in each
# run may or may not find.
#
# It prints the runs that differ from the first, with a diff, and exits 1 if
# any does. The outputs are kept in a directory it names.
set -eu

if [ "${VEGO_REPEAT_SCOPED:-}" != 1 ]; then
	VEGO_REPEAT_SCOPED=1 exec systemd-run --user --scope --quiet -p MemoryMax=12G -p MemorySwapMax=4G -- \
		env VEGO_REPEAT_SCOPED=1 "$0" "$@"
fi

filling=
if [ "${1:-}" = -filling ]; then
	filling=1
	shift
fi
if [ $# -lt 3 ]; then
	echo "usage: repeat.sh [-filling] LAAS DIR RUNS [laas arguments...]" >&2
	exit 2
fi
laas=$(realpath "$1")
dir=$2
runs=$3
shift 3
case $runs in
'' | *[!0-9]*)
	echo "repeat.sh: RUNS must be a number from 2 to 50, not $runs" >&2
	exit 2
	;;
esac
if [ "$runs" -lt 2 ] || [ "$runs" -gt 50 ]; then
	echo "repeat.sh: RUNS must be from 2 to 50, not $runs" >&2
	exit 2
fi

out=$(mktemp -d "${TMPDIR:-/tmp}/vego-repeat.XXXXXX")
echo "repeat.sh: $runs runs of $laas in $dir, two at a time; outputs in $out"

# one runs laas once and writes what it printed, normalized, to $out/N.
one() {
	n=$1
	shift
	status=0
	(cd "$dir" && timeout 1800 "$laas" "$@") >"$out/$n.raw" 2>&1 || status=$?
	{
		if [ -n "$filling" ]; then
			awk '
				/^Answers of Z3 read from the answer cache: / { skip = 3; next }
				skip > 0 { skip--; next }
				/: vego: [0-9]+ of the [0-9]+ answers of Z3 for .* came from the answer cache in / { next }
				/^vego: [0-9]+ of the [0-9]+ answers of Z3 for .* came from the answer cache in / { next }
				{ sub(/, [0-9]+ answered from the answer cache on disk$/, ""); print }
			' "$out/$n.raw"
		else
			cat "$out/$n.raw"
		fi | sed -E 's/^(.*: vego cost of .*, [0-9]+ bytes), [0-9]+\.[0-9]+ s/\1/' | LC_ALL=C sort
		echo "exit status $status"
	} >"$out/$n"
}

n=1
while [ "$n" -le "$runs" ]; do
	one "$n" "$@" &
	if [ $((n + 1)) -le "$runs" ]; then
		one $((n + 1)) "$@" &
	fi
	wait
	n=$((n + 2))
done

differ=0
n=2
while [ "$n" -le "$runs" ]; do
	if ! cmp -s "$out/1" "$out/$n"; then
		differ=$((differ + 1))
		echo "run $n differs from run 1:"
		diff "$out/1" "$out/$n" || true
	fi
	n=$((n + 1))
done
echo "repeat.sh: $differ of the $((runs - 1)) runs after the first differ from it; $(wc -l <"$out/1") lines each, the last \"$(tail -n 1 "$out/1")\""
[ "$differ" -eq 0 ]
