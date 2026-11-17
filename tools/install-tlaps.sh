#!/bin/bash
# Fetch the pinned TLA+ Proof System (TLAPS) release into tools/tlaps-<version>/ (not tracked:
# about 50 MB compressed, with Isabelle, Z3, Zenon and LS4 included). tools/tlapm runs it, and every
# proof results file prints the binary's sha256. On the pin's platform (Linux x86_64) the tarball
# comes from the kept copy tools/TLAPS-PIN names (url), checked against tarball_sha256, so it is the
# pinned binary. On macOS arm64 it comes from upstream's release tag, which is rebuilt under the same
# name: the wrapper will refuse that binary unless TLAPM_UNPINNED=1, and a results file it writes
# says which prover was used.
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
if [ "$PLATFORM" = "$(pin_field platform)" ] && [ -n "$(pin_field url)" ]; then
  url="$(pin_field url)"
  echo "Downloading the pinned $tarball from $url..."
else
  url="https://github.com/tlaplus/tlapm/releases/download/$VERSION/$tarball"
  echo "No pinned build for $PLATFORM; downloading upstream's $tarball (the tag is rebuilt, so the binary may differ)..."
fi
tmp="$(mktemp)"
curl -L --fail -o "$tmp" "$url"
if [ "$PLATFORM" = "$(pin_field platform)" ]; then
  have="$(sha "$tmp")"; want="$(pin_field tarball_sha256)"
  [ "$have" = "$want" ] || { echo "Downloaded tarball is sha256 $have, not the pinned $want"; rm -f "$tmp"; exit 1; }
fi
mkdir -p "$DEST"
tar -xzf "$tmp" -C "$DEST" --strip-components=1
rm -f "$tmp"
[ -x "$DEST/bin/tlapm" ] || { echo "Install failed: $DEST/bin/tlapm is missing"; exit 1; }
echo "Installed $DEST/bin/tlapm (tlapm $("$DEST/bin/tlapm" --version))."
check_pin
