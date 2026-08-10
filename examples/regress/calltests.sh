#!/bin/bash
# Runs coqc on every .v file under examples/regress (this script's directory), regardless of
# where it's invoked from. Each file is compiled with its own directory as the working
# directory, since the LoadPath and smt2/proof file paths inside each .v file are relative to
# the file's own location.
#
# Usage: ./calltests.sh [timeout_seconds]
#   timeout_seconds: per-file timeout, default 120

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

TIMEOUT="${1:-120}"
LOG_FILE="$SCRIPT_DIR/calltests.log"
> "$LOG_FILE"

total=0
n_true=0
n_false=0
n_error=0
n_timeout=0
failed_files=()

while IFS= read -r -d '' vfile; do
  total=$((total + 1))
  dir="$(dirname "$vfile")"
  base="$(basename "$vfile")"
  rel="${vfile#./}"

  echo "==== $rel ====" >> "$LOG_FILE"
  output="$(cd "$dir" && timeout "$TIMEOUT" coqc "$base" 2>&1)"
  status=$?
  echo "$output" >> "$LOG_FILE"
  echo >> "$LOG_FILE"

  if [ "$status" -eq 124 ]; then
    echo "TIMEOUT  $rel"
    n_timeout=$((n_timeout + 1))
    failed_files+=("TIMEOUT  $rel")
  elif [ "$status" -ne 0 ]; then
    echo "ERROR    $rel"
    n_error=$((n_error + 1))
    failed_files+=("ERROR    $rel")
  elif echo "$output" | grep -q "= true"; then
    echo "TRUE     $rel"
    n_true=$((n_true + 1))
  elif echo "$output" | grep -q "= false"; then
    echo "FALSE    $rel"
    n_false=$((n_false + 1))
    failed_files+=("FALSE    $rel")
  else
    echo "OK       $rel"
    n_true=$((n_true + 1))
  fi
done < <(find . -name "*.v" -print0 | sort -z)

echo
echo "===================================================="
echo "Total: $total   True/OK: $n_true   False: $n_false   Error: $n_error   Timeout: $n_timeout"
echo "Full output logged to: $LOG_FILE"
if [ "${#failed_files[@]}" -gt 0 ]; then
  echo
  echo "Non-passing files:"
  printf '  %s\n' "${failed_files[@]}"
fi
