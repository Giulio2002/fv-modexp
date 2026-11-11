#!/bin/bash
# janus verify of row 1 (amd64, error path) with the provenance-fixed binary (agent top)
cd /srv/fv-modexp-top
JANUS=/srv/fv-modexp-ops/janus-provfix
HB=/srv/fv-modexp/build
export JANUS_CACHE_DIR=/srv/fv-modexp-ops/cache-top LEAN_NUM_THREADS=4 JANUS_MEM_MAX=16G
out=build/rows/ex-amd64-RunErr; rm -rf $out
log=build/rows/log-amd64-RunErr
t0=$(date +%s)
$JANUS extract $HB/harness-amd64 'github.com/ethereum/go-ethereum/core/vm.(*bigModExp).Run' $out $(. scripts/contract-flags.sh; contract_flags Run) --max-functions 100 > $log 2>&1 || { echo extract-failed >> $log; exit 1; }
timeout 900 memcap -m 16G $JANUS verify $out --proof lean/FvModexp/Proofs/Amd64/Top/RunErr.lean --proof-root lean \
  --theorem FvModexp.Amd64.Run.correctness --theorem FvModexp.Amd64.Run.Witness.nonvacuous >> $log 2>&1
echo "rc=$? wall=$(( $(date +%s) - t0 ))" >> $log
grep -o '"peakBytes": *[0-9]*' $out/verified.json >> $log 2>/dev/null
