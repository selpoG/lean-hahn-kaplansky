/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import HahnKaplanskyRealClosedness

/-
# Public theorem audit

Run this file with:

    lake env lean HahnKaplanskyRealClosedness/AxiomAudit.lean

The guards reject changes to the dependencies of the public completion points.
The allowed dependencies are the standard classical Lean/mathlib axioms:
propext, Classical.choice, and Quot.sound.
-/

open HahnKaplanskyRealClosedness

#check hahnKaplansky_realClosed_of_realClosed_divisible
#check puiseuxSeries_isRealClosed
#check instIsRealClosedReal
#check realPuiseuxSeries_isRealClosed
#check realRationalHahnField_isRealClosed

/--
info: 'HahnKaplanskyRealClosedness.hahnKaplansky_realClosed_of_realClosed_divisible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hahnKaplansky_realClosed_of_realClosed_divisible

/--
info: 'HahnKaplanskyRealClosedness.puiseuxSeries_isRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms puiseuxSeries_isRealClosed

/--
info: 'HahnKaplanskyRealClosedness.instIsRealClosedReal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms instIsRealClosedReal

/--
info: 'HahnKaplanskyRealClosedness.realPuiseuxSeries_isRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms realPuiseuxSeries_isRealClosed

/--
info: 'HahnKaplanskyRealClosedness.realRationalHahnField_isRealClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms realRationalHahnField_isRealClosed
