import Extracted
import FvModexp.Spec

/-! Cache warm-up module for `scripts/verify-all.sh` (not a row, never claimed): `janus verify` of this file against any extraction
builds the Janus framework and the consumer dependency closure (EthLib, `FvModexp.Spec`) into a fresh `JANUS_CACHE_DIR`, so that the
per-row caps measure the rows only. -/

namespace FvModexp.Warmup

theorem correctness : Extracted.entry = Extracted.entry := rfl

end FvModexp.Warmup
