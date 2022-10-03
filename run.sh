set -Eeuxo pipefail

PASSLIB=~/hw2/build/HW2/LLVMHW2.so        # Specify your build directory in the project
TARGET=${1%.*}
PASS=${@:2}                # Choose either -fplicm-correctness or -fplicm-performance

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
opt -enable-new-pm=0 -loop-simplify ${TARGET}.bc -o ${TARGET}.ls.bc
# Instrument profiler
opt -enable-new-pm=0 -pgo-instr-gen -instrprof ${TARGET}.ls.bc -o ${TARGET}.ls.prof.bc
# Generate binary executable with profiler embedded
clang -fprofile-instr-generate ${TARGET}.ls.prof.bc -o ${TARGET}_prof

# Generate profiled data
./${TARGET}_prof > correct_output
llvm-profdata merge -o ${TARGET}.profdata default.profraw

# Apply FPLICM
opt -enable-new-pm=0 -o ${TARGET}.fplicm.bc -pgo-instr-use -pgo-test-profile-file=${TARGET}.profdata -load ${PASSLIB} ${PASS} < ${TARGET}.ls.bc &> opt_output

# Generate binary excutable before FPLICM: Unoptimzied code
llvm-dis ${TARGET}.ls.bc -o=no_fplicm.ll
clang -S ${TARGET}.ls.bc -o no_fplicm.s
clang ${TARGET}.ls.bc -o ${TARGET}_no_fplicm
# Generate binary executable after FPLICM: Optimized code
llvm-dis ${TARGET}.fplicm.bc -o=fplicm.ll
clang -S ${TARGET}.fplicm.bc -o fplicm.s
clang ${TARGET}.fplicm.bc -o ${TARGET}_fplicm

# Produce output from binary to check correctness
./${TARGET}_fplicm > fplicm_output

set +x

echo -e "\n=== Correctness Check ==="
if [ "$(diff correct_output fplicm_output)" != "" ]; then
    echo -e ">> FAIL\n"
    exit 1
else
    echo -e ">> PASS\n"
    # Measure performance
    echo -e "1. Performance of unoptimized code"
    time ./${TARGET}_no_fplicm > /dev/null
    echo -e "\n\n"
    echo -e "2. Performance of optimized code"
    time ./${TARGET}_fplicm > /dev/null
    echo -e "\n\n"
fi
