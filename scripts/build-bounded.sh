#!/usr/bin/env bash
# One Lake dependency graph, with an explicit cap on concurrent Lean compilers.
# The official toolchain is untouched; a temporary sysroot links to its files.
set -euo pipefail
cd "$(dirname "$0")/.."
jobs="${STICKY_BUILD_JOBS:-3}"
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || { echo 'STICKY_BUILD_JOBS must be positive' >&2; exit 2; }
command -v flock >/dev/null
real_lean="$(elan which lean)"
real_root="$(dirname "$(dirname "$real_lean")")"
shim="$(mktemp -d "${TMPDIR:-/tmp}/sticky-lean-build.XXXXXX")"
trap 'rm -rf "$shim"' EXIT
mkdir -p "$shim/bin" "$shim/locks"
for item in "$real_root"/*; do
  name="$(basename "$item")"
  [[ "$name" == bin ]] || ln -s "$item" "$shim/$name"
done
for item in "$real_root/bin"/*; do
  name="$(basename "$item")"
  [[ "$name" == lean ]] || ln -s "$item" "$shim/bin/$name"
done
cat > "$shim/bin/lean" <<'WRAPPER'
#!/usr/bin/env bash
set -euo pipefail
case "${1:-}" in
  --version|--githash|--print-prefix|--print-libdir|--help|-h)
    exec "$STICKY_REAL_LEAN" "$@" ;;
esac
while :; do
  for ((slot=1; slot<=STICKY_BUILD_JOBS; slot++)); do
    exec 9>"$STICKY_BUILD_LOCKS/$slot.lock"
    if flock -n 9; then
      export LEAN_NUM_THREADS="${STICKY_LEAN_THREADS:-1}"
      exec "$STICKY_REAL_LEAN" "$@"
    fi
    exec 9>&-
  done
  sleep 0.1
done
WRAPPER
chmod +x "$shim/bin/lean"
export STICKY_REAL_LEAN="$real_lean" STICKY_BUILD_JOBS="$jobs"
export STICKY_BUILD_LOCKS="$shim/locks"
export LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT="$shim"
if [[ "${1:-}" == --check-cache ]]; then
  shift
  "$real_root/bin/lake" --no-build build "$@"
else
  printf 'Using official Lean through a %s-compiler semaphore\n' "$jobs"
  "$real_root/bin/lake" build "$@"
fi
