#!/bin/bash
# Fetch the pinned TLA+ Proof System (TLAPS) release into tools/tlaps-<version>/ (not tracked:
# about 50 MB compressed, with Isabelle, Z3, Zenon and LS4 included). tools/tlapm runs it, and every
# proof results file prints the binary's sha256. Prebuilt for Linux x86_64 and macOS arm64 only;
# tools/TLAPS-PIN records the Linux build, so on macOS the wrapper will refuse the binary unless
# TLAPM_UNPINNED=1, and the results files will say which prover was used.
set -e
TOOLS_DIR="$(cd "$(dirname "$0")" && pwd)"
pin_field() { grep -E "^$1 " "$TOOLS_DIR/TLAPS-PIN" | head -1 | cut -d' ' -f2-; }
VERSION="$(pin_field version)"
DEST="$TOOLS_DIR/tlaps-$VERSION"
sha() { if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -d' ' -f1; }
check_pin() {
  have="$(sha "$DEST/bin/tlapm")"; want="$(pin_field binary_sha256)"
  if [ "$have" = "$want" ]; then
    echo "Matches tools/TLAPS-PIN (commit $(pin_field commit))."
  else
    echo "Does NOT match tools/TLAPS-PIN: pinned $want (commit $(pin_field commit)),"
    echo "installed $have (tlapm $("$DEST/bin/tlapm" --version)). The release tag was rebuilt upstream."
    echo "tools/tlapm refuses this binary unless TLAPM_UNPINNED=1; moving the pin is the record of a new prover."
  fi
}
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) PLATFORM="arm64-darwin" ;;
  Linux-x86_64) PLATFORM="x86_64-linux-gnu" ;;
  *) echo "No prebuilt TLAPS $VERSION for $(uname -s) $(uname -m)"; exit 1 ;;
esac
if [ -x "$DEST/bin/tlapm" ]; then
  echo "tlapm is present at $DEST/bin/tlapm; remove the directory to reinstall."
  check_pin; exit 0
fi
tarball="tlapm-$VERSION-$PLATFORM.tar.gz"
echo "Downloading $tarball..."
mkdir -p "$DEST"
curl -L --fail "https://github.com/tlaplus/tlapm/releases/download/$VERSION/$tarball" \
  | tar -xzf - -C "$DEST" --strip-components=1
[ -x "$DEST/bin/tlapm" ] || { echo "Install failed: $DEST/bin/tlapm is missing"; exit 1; }
echo "Installed $DEST/bin/tlapm (tlapm $("$DEST/bin/tlapm" --version))."
check_pin
