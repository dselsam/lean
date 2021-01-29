#!/usr/bin/env bash
# Usage: mk_all.sh [subdirectory]
#
# Examples:
#   ./scripts/mk_all.sh
#   ./scripts/mk_all.sh data/
#
# Makes a <lean3>/library/$directory/all.lean importing all files inside $directory.
# If $directory is omitted, creates `<lean3>/library/all.lean`.

cd "$( dirname "${BASH_SOURCE[0]}" )"/../library
if [[ $# = 1 ]]; then
  dir="$1"
else
  dir="."
fi

find "$dir" -name \*.lean -not -name all.lean \
  | sed 's,^\./,,;s,\.lean$,,;s,/,.,g;s,^,import ,' \
  | sort >"$dir"/all.lean
