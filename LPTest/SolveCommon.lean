/-
  Shared scaffolding for the SoPlex-backed tests. Pulls in `LP`;
  pure-verifier tests stay on `LPTest.Common` alone.
-/

import LPTest.Common
import LP

namespace LPTest

open LP

/-- Solver options used by every backed-by-SoPlex test in this suite:
    presolve off (so the exact certificate is against the original LP),
    non-verbose, no precision boost. -/
def noPresolve : Options :=
  { ({} : Options) with presolve := false, verbose := false, precisionBoost := false }

end LPTest
