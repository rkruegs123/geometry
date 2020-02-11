import Geo.Geo.Core

namespace Geo

open Triangle
open WithInst
open Angle

def IMO_2014_P4 : Prop :=
∀ (A B C M N P Q : Point),
acute ⟨A, B, C⟩ →
on P (Seg.mk B C) →
on Q (Seg.mk B C) →
uangle ⟨P, A, B⟩ = uangle ⟨B, C, A⟩ →
uangle ⟨C, A, Q⟩ = uangle ⟨A, B, C⟩ →
on M (Line.mk A P) →
on N (Line.mk A Q) →
P = midp (Seg.mk A M) → -- ryankrue: note how we don't use let here
Q = midp (Seg.mk A N) → -- ryankrue: and here
allIntersect₂ [intersectElem $ Line.mk B M, intersectElem $ Line.mk C N, intersectElem $ circumcircle ⟨A, B, C⟩]

end Geo
