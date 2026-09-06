/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness

namespace HahnKaplanskyRealClosedness

variable (k Γ : Type*)
variable [Field k] [LinearOrder k] [IsStrictOrderedRing k] [IsRealClosed k]
variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [DivisibleBy Γ ℕ]

/- The canonical public theorem is usable without historical continuation inputs. -/
example : IsRealClosed (HahnField k Γ) :=
  hahnKaplansky_realClosed_of_realClosed_divisible k Γ

example : IsRealClosed (HahnField ℝ ℚ) :=
  realRationalHahnField_isRealClosed

end HahnKaplanskyRealClosedness
