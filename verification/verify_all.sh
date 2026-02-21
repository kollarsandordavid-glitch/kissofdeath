#!/usr/bin/env bash

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "========================================="
echo "JAIDE v40 Formal Verification Suite"
echo "========================================="
echo ""

TOTAL_CHECKS=0
PASSED_CHECKS=0
FAILED_CHECKS=0

run_check() {
    local name="$1"
    shift
    local -a cmd_args=("$@")
    
    TOTAL_CHECKS=$((TOTAL_CHECKS + 1))
    echo -n "[$TOTAL_CHECKS] Checking $name... "
    
    if "${cmd_args[@]}" > "/tmp/verification_${TOTAL_CHECKS}.log" 2>&1; then
        echo "PASSED"
        PASSED_CHECKS=$((PASSED_CHECKS + 1))
    else
        echo "FAILED"
        FAILED_CHECKS=$((FAILED_CHECKS + 1))
        echo "  Error log: /tmp/verification_${TOTAL_CHECKS}.log"
        head -20 "/tmp/verification_${TOTAL_CHECKS}.log"
    fi
}

echo "========================================="
echo "Agda Verification"
echo "========================================="

if command -v agda &> /dev/null; then
    run_check "Agda Types" agda --safe agda/Types.agda
    run_check "Agda Memory" agda --safe agda/Memory.agda
    run_check "Agda Tensor" agda --safe agda/Tensor.agda
    run_check "Agda RSF" agda --safe agda/RSF.agda
    run_check "Agda Tokenizer" agda --safe agda/Tokenizer.agda
    run_check "Agda Optimizer" agda --safe agda/Optimizer.agda
else
    echo "Agda not found, skipping Agda verification"
fi

echo ""
echo "========================================="
echo "Lean4 Verification"
echo "========================================="

if command -v lake &> /dev/null; then
    cd lean4
    run_check "Lean4 Build" lake build
    cd ..
else
    echo "Lean4/lake not found, skipping Lean4 verification"
fi

echo ""
echo "========================================="
echo "Isabelle Verification"
echo "========================================="

if command -v isabelle &> /dev/null; then
    run_check "Isabelle Types" isabelle build -d isabelle -v Types
    run_check "Isabelle Memory" isabelle build -d isabelle -v Memory
    run_check "Isabelle Tensor" isabelle build -d isabelle -v Tensor
    run_check "Isabelle RSF" isabelle build -d isabelle -v RSF
else
    echo "Isabelle not found, skipping Isabelle verification"
fi

echo ""
echo "========================================="
echo "Viper Verification"
echo "========================================="

if command -v silicon &> /dev/null; then
    run_check "Viper Memory" silicon viper/Memory.vpr
    run_check "Viper Tensor" silicon viper/Tensor.vpr
else
    echo "Viper/silicon not found, skipping Viper verification"
fi

echo ""
echo "========================================="
echo "TLA+ Verification"
echo "========================================="

if command -v tlc &> /dev/null; then
    run_check "TLA+ TensorSpec" tlc tla/TensorSpec.tla
    run_check "TLA+ MemorySpec" tlc tla/MemorySpec.tla
else
    echo "TLA+/tlc not found, skipping TLA+ verification"
fi

echo ""
echo "========================================="
echo "Spin/Promela Verification"
echo "========================================="

if command -v spin &> /dev/null; then
    cd spin
    run_check "Spin TensorModel" bash -c "spin -a TensorModel.pml && gcc -o pan pan.c && ./pan -a"
    run_check "Spin MemoryModel" bash -c "spin -a MemoryModel.pml && gcc -o pan pan.c && ./pan -a"
    cd ..
else
    echo "Spin not found, skipping Spin verification"
fi

echo ""
echo "========================================="
echo "Verification Summary"
echo "========================================="
echo "Total checks: $TOTAL_CHECKS"
echo "Passed: $PASSED_CHECKS"
echo "Failed: $FAILED_CHECKS"
echo ""

if [ $FAILED_CHECKS -eq 0 ]; then
    echo "All verification checks passed!"
    exit 0
else
    echo "Some verification checks failed"
    exit 1
fi
