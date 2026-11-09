#!/bin/bash
# Install TLA+ tools locally to this repository

set -e

TLA_VERSION="$(grep -E '^version ' tools/TLC-PIN | cut -d' ' -f2)"   # tools/TLC-PIN
TLA_JAR="tla2tools.jar"
TOOLS_DIR="tools"

echo "Installing TLA+ tools version $TLA_VERSION..."

# Create tools directory
mkdir -p "$TOOLS_DIR"

# Download tla2tools.jar
echo "Downloading tla2tools.jar..."
curl -L "https://github.com/tlaplus/tlaplus/releases/download/$TLA_VERSION/$TLA_JAR" \
  -o "$TOOLS_DIR/$TLA_JAR"

# Verify download against the pin every results file cites
if [ ! -f "$TOOLS_DIR/$TLA_JAR" ]; then
  echo "✗ Failed to download $TLA_JAR"
  exit 1
fi
want="$(grep -E '^jar_sha256 ' tools/TLC-PIN | cut -d' ' -f2)"
have="$( (sha256sum "$TOOLS_DIR/$TLA_JAR" 2>/dev/null || shasum -a 256 "$TOOLS_DIR/$TLA_JAR") | cut -d' ' -f1)"
if [ "$have" = "$want" ]; then
  echo "✓ Installed $TOOLS_DIR/$TLA_JAR, sha256 $have (matches tools/TLC-PIN)"
else
  echo "✗ $TOOLS_DIR/$TLA_JAR is sha256 $have, not the pinned $want (tools/TLC-PIN)."
  echo "  scripts/tlc_rows.py refuses it unless TLC_UNPINNED=1."
fi

# Create convenience wrapper scripts
cat > tlc << 'EOF'
#!/bin/bash
# TLC wrapper script
java -XX:+UseParallelGC -jar "$(dirname "$0")/tools/tla2tools.jar" "$@"
EOF

cat > tlc-workers << 'EOF'
#!/bin/bash
# TLC wrapper with auto workers (uses all CPU cores)
java -XX:+UseParallelGC -jar "$(dirname "$0")/tools/tla2tools.jar" -workers auto "$@"
EOF

chmod +x tlc tlc-workers

echo ""
echo "✓ Installation complete!"
echo ""
echo "Created convenience scripts:"
echo "  ./tlc          - Run TLC model checker"
echo "  ./tlc-workers  - Run TLC with auto workers (parallel)"
echo ""
echo "For proofs, also run tools/install-tlaps.sh."
echo ""
echo "Usage examples:"
echo "  ./tlc -parse Constitution.tla"
echo "  ./tlc -simulate -depth 40 -config Constitution.cfg Constitution.tla"
echo "  ./tlc-workers -config Judiciary.cfg Judiciary.tla"
echo ""
