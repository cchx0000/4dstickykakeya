#!/usr/bin/env bash
# One Lake dependency graph, with a shared cap on all task Lean compilers.
# The official toolchain is untouched; a temporary sysroot links to its files.
set -euo pipefail
cd "$(dirname "$0")/.."
jobs="${STICKY_BUILD_JOBS:-2}"
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || { echo 'STICKY_BUILD_JOBS must be positive' >&2; exit 2; }
command -v flock >/dev/null
real_lean="${STICKY_LEAN_BINARY:-$(elan which lean)}"
real_root="$(dirname "$(dirname "$real_lean")")"
shim="$(mktemp -d "${TMPDIR:-/tmp}/sticky-lean-build.XXXXXX")"
trap 'rm -rf "$shim"' EXIT
global_locks="${STICKY_GLOBAL_LOCK_DIR:-$PWD/.lake/global-lean-locks}"
mkdir -p "$shim/bin" "$global_locks"
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
export LEAN_NUM_THREADS="${STICKY_LEAN_THREADS:-1}"
exec python3 "$STICKY_LEAN_SLOT" --slots "$STICKY_BUILD_JOBS" \
  --lock-dir "$STICKY_BUILD_LOCKS" -- "$STICKY_REAL_LEAN" "$@"
WRAPPER
chmod +x "$shim/bin/lean"
export STICKY_REAL_LEAN="$real_lean" STICKY_BUILD_JOBS="$jobs"
export STICKY_BUILD_LOCKS="$global_locks"
export STICKY_LEAN_SLOT="$PWD/scripts/lean-slot.py"
export LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT="$shim"
if [[ "${1:-}" == --check-cache ]]; then
  shift
  "$real_root/bin/lake" --no-build build "$@"
else
  printf 'Using official Lean through a %s-compiler semaphore\n' "$jobs"
  "$real_root/bin/lake" build "$@"
fi
