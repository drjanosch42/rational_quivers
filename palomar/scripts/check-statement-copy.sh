#!/usr/bin/env bash
# The definitions block of Challenge.lean and of RQPalomar/Statement.lean must be byte-identical,
# and both files must have the same import lines; otherwise Comparator will (correctly) reject.
set -euo pipefail
cd "$(dirname "$0")/.."
block() { sed -n '/^-- BEGIN STATEMENT DEFINITIONS/,/^-- END STATEMENT DEFINITIONS/p' "$1"; }
imports() { grep -E '^(public )?import ' "$1"; }
diff <(block Challenge.lean) <(block RQPalomar/Statement.lean)
diff <(imports Challenge.lean) <(imports RQPalomar/Statement.lean)
echo "statement copy: identical"
