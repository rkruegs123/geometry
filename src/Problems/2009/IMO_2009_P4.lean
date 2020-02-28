/-
IMO 2009 P4 is a determined problem. The problem statement is as follows:

"Find all possible values of <CAB."

This problem statement is replaced by the disjunctive witnesses in this formalization.

Solution: https://web.evanchen.cc/exams/IMO-2009-notes.pdf
-/

import Geo.Geo.Core

namespace Geo

open Analytic Angle Seg Triangle

def IMO_2009_P4 : Prop :=
∀ (A B C D E : Point),
cong ⟨A, B⟩ ⟨A, C⟩ →
intersectAt (bisector ⟨C, A, B⟩) (Seg.mk B C) D →
intersectAt (bisector ⟨A, B, C⟩) (Seg.mk C A) E →
let K := incenter ⟨A, D, C⟩;
degToRadians 45 = uangle ⟨B, E, K⟩ →
-- The following is a disjunctive witness to the determined problem
degToRadians 60 = uangle ⟨C, A, B⟩ ∨ degToRadians 90 = uangle ⟨C, A, B⟩

end Geo
