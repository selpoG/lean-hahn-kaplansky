/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness.Puiseux
import HahnKaplanskyRealClosedness.RealClosedReal
import HahnKaplanskyRealClosedness.Main

namespace HahnKaplanskyRealClosedness

/-- The Puiseux series field over the real numbers is real closed. -/
theorem realPuiseuxSeries_isRealClosed :
    IsRealClosed (PuiseuxSeries ℝ) :=
  puiseuxSeries_isRealClosed ℝ

/-- The Hahn field with real coefficients and rational value group is real closed. -/
theorem realRationalHahnField_isRealClosed :
    IsRealClosed (HahnField ℝ ℚ) :=
  hahnKaplansky_realClosed_of_realClosed_divisible ℝ ℚ

end HahnKaplanskyRealClosedness
