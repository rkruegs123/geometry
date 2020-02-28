import Geo.Geo.Core

namespace Geo

open Angle Triangle

def IMO_2014_P4 : Prop :=
∀ (A B C M N P Q : Point),
acute ⟨A, B, C⟩ →
on P (Seg.mk B C) →
on Q (Seg.mk B C) →
uangle ⟨P, A, B⟩ = uangle ⟨B, C, A⟩ →
uangle ⟨C, A, Q⟩ = uangle ⟨A, B, C⟩ →
on M (Line.mk A P) →
on N (Line.mk A Q) →
Seg.isMidpoint P ⟨A, M⟩ → -- note how we don't use let here
Seg.isMidpoint Q ⟨A, N⟩ → -- and here
allIntersect₂ [Line.mk B M, Line.mk C N] [circumcircle ⟨A, B, C⟩]

end Geo
