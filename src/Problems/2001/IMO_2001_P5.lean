/-
IMO 2001 P5 is a "determine" problem. The problem statement is as follows:

"What are the possible angles of triangle ABC?"

This problem statement is replaced by the last two witnesses in this formalization.

Solution: https://web.evanchen.cc/exams/IMO-2001-notes.pdf
-/

import Geo.Geo.Core

namespace Geo

open Analytic Angle

def IMO_2001_P5 : Prop :=
∀ (A B C P Q : Point),
isBisector ⟨A, P⟩ ⟨B, A, C⟩ →
on P (Seg.mk B C) →
isBisector ⟨B, Q⟩ ⟨A, B, C⟩ →
on Q (Seg.mk C A) →
deg2π 60 = uangle ⟨B, A, C⟩ →
ulen (Seg.mk A B) + ulen (Seg.mk B P) = ulen (Seg.mk A Q) + ulen (Seg.mk Q B) →
-- For now we hardcode the desired goal
-- TODO: use `determine` construct
deg2π 80 = uangle ⟨C, B, A⟩ ∧ deg2π 40 = uangle ⟨A, C, B⟩

end Geo
