/-
IMO 2001 P5 is a determined problem. The problem statement is as follows:

"What are the possible angles of triangle ABC?"

This problem statement is replaced by the last two witnesses in this formalization.

Solution: https://web.evanchen.cc/exams/IMO-2001-notes.pdf
-/

import Geo.Geo.Core

namespace Geo

def IMO_2001_P5 : Prop :=
∀ (A B C P Q : Point),
Angle.isBisector ⟨A, P⟩ ⟨B, A, C⟩ →
on P (Seg.mk B C) →
Angle.isBisector ⟨B, Q⟩ ⟨A, B, C⟩ →
on Q (Seg.mk C A) →
Analytic.degToRadians 60 = uangle ⟨B, A, C⟩ →
ulen (Seg.mk A B) + ulen (Seg.mk B P) = ulen (Seg.mk A Q) + ulen (Seg.mk Q B) →
Analytic.degToRadians 80 = uangle ⟨C, B, A⟩ → -- witness to determined problem
Analytic.degToRadians 40 = uangle ⟨A, C, B⟩ -- witness to determined problem
-- NOTE: Solution is trivial given the above witnesses

end Geo
