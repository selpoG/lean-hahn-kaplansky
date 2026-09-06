/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness

namespace HahnKaplanskyRealClosedness

variable (k : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k] [IsRealClosed k]

example {x : PuiseuxSeries k} (hx : 0 ≤ x) : IsSquare x :=
  puiseuxSeries_isSquare_of_nonneg k hx

example : IsRealClosed (PuiseuxSeries k) :=
  puiseuxSeries_isRealClosed k

example : IsRealClosed (PuiseuxSeries ℝ) :=
  realPuiseuxSeries_isRealClosed

end HahnKaplanskyRealClosedness
