set -Eeuxo pipefail

for i in 1 2 3 4 5 6
do
  ./run.sh tests/hw2correct${i}.c -fplicm-correctness
  cp tests/hw2correct${i}.fplicm.bc benchmarks/hw2correct${i}_base.bc
done

for i in 1 2 3 4 5 6
do
  ./run.sh tests/hw2correct${i}.c -fplicm-performance
  cp tests/hw2correct${i}.fplicm.bc benchmarks/hw2correct${i}_bonus.bc
done

for i in 1 2 3 4
do
  ./run.sh tests/hw2perf${i}.c -fplicm-performance
  cp tests/hw2perf${i}.fplicm.bc benchmarks/hw2perf${i}_bonus.bc
done
