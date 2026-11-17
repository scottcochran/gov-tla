#!/bin/bash
# Check tools/TLA-KIT-PIN before anything runs in the image it names. Needs docker and an authenticated gh.
#   1. jar_sha256 equals tools/TLC-PIN's jar_sha256: the image's TLC is the one every TLC results file cites.
#   2. The digest is one tla-kit's release workflow published: its provenance attestation verifies against
#      scottcochran/tla-kit (gh attestation verify).
#   3. The image is what the pin says: its revision label is `commit`, and its jar, tlapm binary and tlapm's
#      reported commit are jar_sha256, tlapm_sha256 and tlapm_commit.
#   4. Reported, not failed: whether tlapm_sha256 is tools/TLAPS-PIN's binary_sha256. While they differ (as they
#      did before the prover pin moved to the image's build, 2026.11.17), CI's proofs job compares counts only.
# Prints the image reference as its last line. Exits non-zero on the first failed check.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
field() { grep -E "^$2 " "$here/$1" | head -1 | cut -d' ' -f2-; }
fail() { echo "FAIL: $*" >&2; exit 1; }

image="$(field TLA-KIT-PIN image)"
[[ "$image" =~ ^ghcr\.io/scottcochran/tla-kit@sha256:[0-9a-f]{64}$ ]] || fail "image is not a ghcr.io/scottcochran/tla-kit digest: $image"

want_jar="$(field TLA-KIT-PIN jar_sha256)"
[ "$want_jar" = "$(field TLC-PIN jar_sha256)" ] || fail "TLA-KIT-PIN jar_sha256 $want_jar is not TLC-PIN's $(field TLC-PIN jar_sha256)"
echo "ok   jar_sha256 equals tools/TLC-PIN"

gh attestation verify "oci://$image" --repo scottcochran/tla-kit >/dev/null || fail "no verified attestation for $image from scottcochran/tla-kit"
echo "ok   provenance attestation verified against scottcochran/tla-kit"

docker pull -q "$image" >/dev/null
rev="$(docker image inspect "$image" --format '{{index .Config.Labels "org.opencontainers.image.revision"}}')"
[ "$rev" = "$(field TLA-KIT-PIN commit)" ] || fail "image revision label $rev is not commit $(field TLA-KIT-PIN commit)"
read -r have_jar have_tlapm have_commit < <(docker run --rm "$image" sh -c \
  'echo $(sha256sum /opt/tla/tla2tools.jar | cut -d" " -f1) $(sha256sum /opt/tlaps/bin/tlapm | cut -d" " -f1) $(tlapm --version)' 2>/dev/null)
[ "$have_jar" = "$want_jar" ] || fail "image jar is $have_jar, not $want_jar"
[ "$have_tlapm" = "$(field TLA-KIT-PIN tlapm_sha256)" ] || fail "image tlapm is $have_tlapm, not $(field TLA-KIT-PIN tlapm_sha256)"
[ "$have_commit" = "$(field TLA-KIT-PIN tlapm_commit)" ] || fail "image tlapm reports $have_commit, not $(field TLA-KIT-PIN tlapm_commit)"
echo "ok   image $(field TLA-KIT-PIN release) at $rev holds the pinned jar and tlapm $have_commit"

if [ "$have_tlapm" = "$(field TLAPS-PIN binary_sha256)" ]; then
  echo "ok   the image's tlapm is tools/TLAPS-PIN's: proofs are regenerated and compared in full"
else
  echo "note the image's tlapm ($have_commit) is not tools/TLAPS-PIN's ($(field TLAPS-PIN commit)): proofs compare counts only"
fi
echo "$image"
