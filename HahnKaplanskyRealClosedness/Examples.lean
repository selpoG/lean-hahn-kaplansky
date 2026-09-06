/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness

/-!
# Public API examples

These examples are intentionally small.  They check the theorem statements that a downstream
user should be able to apply without importing proof-internal modules or supplying historical
continuation data.
-/

namespace HahnKaplanskyRealClosedness

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k] [IsRealClosed k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ]

example : IsRealClosed (HahnField k Γ) :=
  hahnKaplansky_realClosed_of_realClosed_divisible k Γ

variable {x : PuiseuxSeries k}

example (hx : 0 ≤ x) : IsSquare x :=
  puiseuxSeries_isSquare_of_nonneg k hx

example : IsRealClosed (PuiseuxSeries k) :=
  puiseuxSeries_isRealClosed k

example : IsRealClosed (PuiseuxSeries ℝ) :=
  realPuiseuxSeries_isRealClosed

example : IsRealClosed (HahnField ℝ ℚ) :=
  realRationalHahnField_isRealClosed

end HahnKaplanskyRealClosedness
