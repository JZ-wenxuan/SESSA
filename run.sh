set -Eeuxo pipefail

PASSLIB=~/proj/build/HW2/LLVMHW2.so        # Specify your build directory in the project
TARGET=${1%.*}
PASS=${@:2}                # Choose either -sessa-correctness or -sessa-performance

# Delete outputs from previous run.
git clean -fXd > /dev/null

# rebuild HW2PASS
mkdir build
cd build
cmake .. &> /dev/null
make -j2
cd ..

# Convert source code to bitcode (IR)
clang -emit-llvm -c -Xclang -disable-O0-optnone ${TARGET}.c -o ${TARGET}.bc
# Canonicalize natural loops
# opt -enable-new-pm=0 -loop-simplify ${TARGET}.bc -o ${TARGET}.bc
# # Instrument profiler
# opt -enable-new-pm=0 -pgo-instr-gen -instrprof ${TARGET}.bc -o ${TARGET}.prof.bc
# # Generate binary executable with profiler embedded
# clang -fprofile-instr-generate ${TARGET}.prof.bc -o ${TARGET}_prof

# # Generate profiled data
# ./${TARGET}_prof > correct_output
# llvm-profdata merge -o ${TARGET}.profdata default.profraw

# Apply sessa
opt -enable-new-pm=0 -o ${TARGET}.sessa.bc -load ${PASSLIB} ${PASS} < ${TARGET}.bc &> opt_output
opt -enable-new-pm=0 -o ${TARGET}.cytron.bc -mem2reg < ${TARGET}.bc &> /dev/null

# Generate binary excutable before ssa construction: Unoptimzied code
llvm-dis ${TARGET}.bc -o=original.ll
clang -S ${TARGET}.bc -o original.s
clang ${TARGET}.bc -o ${TARGET}_original
# Generate binary excutable after cytron
llvm-dis ${TARGET}.cytron.bc -o=cytron.ll
clang -S ${TARGET}.cytron.bc -o cytron.s
clang ${TARGET}.cytron.bc -o ${TARGET}_cytron
# Generate binary executable after sessa
llvm-dis ${TARGET}.sessa.bc -o=sessa.ll
clang -S ${TARGET}.sessa.bc -o sessa.s
clang ${TARGET}.sessa.bc -o ${TARGET}_sessa

# Produce output from binary to check correctness
./${TARGET}_sessa > sessa_output
./${TARGET}_original > correct_output

set +x

echo -e "\n=== Correctness Check ==="
if [ "$(diff correct_output sessa_output)" != "" ]; then
    echo -e ">> FAIL\n"
    exit 1
else
    echo -e ">> PASS\n"
    # # Measure performance
    # echo -e "1. Performance of unoptimized code"
    # time ./${TARGET}_cytron > /dev/null
    # echo -e "\n\n"
    # echo -e "2. Performance of optimized code"
    # time ./${TARGET}_sessa > /dev/null
    # echo -e "\n\n"
fi
