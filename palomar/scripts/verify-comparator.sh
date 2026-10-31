#!/usr/bin/env bash
set -euo pipefail

# Judge Solution against Challenge the way Palomar does: with the `lake
# comparator` that ships in this project's own toolchain, replaying the proof
# through Lean's kernel and the toolchain's bundled independent kernels
# (NanoDa and con-ron). Nothing is built from a pin; everything that judges
# comes from `lean-toolchain`, which Palomar requires to be v4.35.0-rc2 or
# later.
#
# Adapted from PalomarTemplate's scripts/verify-comparator.sh. This project
# requires the formalization `../lean` as a path dependency, and the sandbox
# of a plain `lake comparator` binds only this directory. So, as Palomar's
# verifier does, the Challenge and the Solution are built with Lake and
# exported with the toolchain's `leanexport` outside that sandbox, and
# `lake comparator` judges the two exports. Extra arguments (for example
# `--paranoid`) are passed on to `lake comparator`.
project_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$project_root"

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

work=$(mktemp -d -t palomar-comparator.XXXXXX)
trap 'rm -rf "$work"' EXIT

# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This
# generated copy does the same, so the local check judges as the registry does.
# The export targets are those Palomar passes to leanexport: Quot and its three
# companions, the theorems, the permitted axioms, the kernel's built-in
# constants (read from the toolchain's Lake/CLI/Check.lean) and the definitions.
python3 - comparator.json "$work" "$prefix" <<'PY'
import json
import pathlib
import re
import sys

source, work, prefix = sys.argv[1:]
work = pathlib.Path(work)
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
(work / "comparator.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

check = pathlib.Path(prefix, "src", "lean", "lake", "Lake", "CLI", "Check.lean").read_text(encoding="utf-8")
match = re.search(r"^def primitiveTargets[^\n]*\n(?P<body>.*?)^def ", check, re.MULTILINE | re.DOTALL)
if match is None:
    print("error: cannot read the toolchain's primitiveTargets", file=sys.stderr)
    raise SystemExit(1)
body = re.sub(r"/-.*?-/", "", match.group("body"), flags=re.DOTALL)
body = "\n".join(line.split("--", 1)[0] for line in body.splitlines())
primitives = re.findall(r"``([A-Za-z_][A-Za-z0-9_'.]*)", body)
axioms = list(config["permitted_axioms"])
builtin = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in axioms else []
targets = [*builtin, *config["theorem_names"], *axioms, *primitives, *config.get("definition_names", [])]
(work / "targets").write_text("\n".join(targets) + "\n", encoding="utf-8")
(work / "modules").write_text(f"{config['challenge_module']}\n{config['solution_module']}\n", encoding="utf-8")
PY

{ read -r challenge_module; read -r solution_module; } < "$work/modules"
mapfile -t targets < "$work/targets"

lake exe cache get
lake build "$challenge_module" "$solution_module"
lake env "$prefix/bin/leanexport" "$challenge_module" -- "${targets[@]}" > "$work/challenge.export"
lake env "$prefix/bin/leanexport" "$solution_module" -- "${targets[@]}" > "$work/solution.export"
lake comparator --config "$work/comparator.json" \
  --challenge-from-export "$work/challenge.export" \
  --solution-from-export "$work/solution.export" "$@"
