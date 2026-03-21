#!/bin/bash
# Test script for jasmin2rocq printer
# Runs jasmin2rocq on all example programs in compiler/examples,
# wraps each output in a .v file, and type-checks with coqc.

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
JASMIN2ROCQ="$ROOT_DIR/compiler/jasmin2rocq"
EXAMPLES_DIR="$ROOT_DIR/compiler/examples"
PROOFS_DIR="$ROOT_DIR/proofs"
OUTDIR=$(mktemp -d)

trap "rm -rf $OUTDIR" EXIT

PASS=0
FAIL=0

# Coqc flags matching _CoqProject
COQC_FLAGS=(
  -R "$PROOFS_DIR/3rdparty" Jasmin
  -R "$PROOFS_DIR/arch" Jasmin
  -R "$PROOFS_DIR/compiler" Jasmin
  -R "$PROOFS_DIR/lang" Jasmin
  -R "$PROOFS_DIR/ssrmisc" Jasmin
  -R "$PROOFS_DIR/itrees" Jasmin
  -w -all
)

# Collect all .jazz files under compiler/examples
FILES=()
while IFS= read -r -d '' f; do
  FILES+=("$f")
done < <(find "$EXAMPLES_DIR" -name '*.jazz' -print0 | sort -z)

echo "Running jasmin2rocq tests on ${#FILES[@]} files..."
echo ""

for jazz_file in "${FILES[@]}"; do
  # Use path relative to examples dir as test name (replacing / and . with _)
  rel_path="${jazz_file#$EXAMPLES_DIR/}"
  test_name=$(echo "$rel_path" | sed 's|[/.-]|_|g; s|_jazz$||')
  v_file="$OUTDIR/test_${test_name}.v"

  # Step 1: Run jasmin2rocq
  rocq_output=$("$JASMIN2ROCQ" "$jazz_file" 2>/dev/null) || {
    echo "FAIL $rel_path (jasmin2rocq failed)"
    FAIL=$((FAIL + 1))
    continue
  }

  # Step 2: Generate .v file with imports and the printer output
  cat > "$v_file" <<ROCQ_EOF
From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ZArith.
Require Import expr ident var type global warray_ pseudo_operator sopn arch_extra.
Require Import x86_decl x86_instr_decl x86_extra.
Import Utf8.

Axiom mkvar : string -> var_i.
Axiom mkfun : string -> funname.
Axiom atoI : arch_toIdent.
#[local] Existing Instance atoI.

${rocq_output}
ROCQ_EOF

  # Step 3: Type-check with coqc
  if coqc "${COQC_FLAGS[@]}" "$v_file" 2>/dev/null; then
    echo "PASS $rel_path"
    PASS=$((PASS + 1))
  else
    echo "FAIL $rel_path"
    FAIL=$((FAIL + 1))
  fi
done

echo ""
echo "Results: $PASS passed, $FAIL failed (total: ${#FILES[@]})"

if [ "$FAIL" -gt 0 ]; then
  exit 1
fi
