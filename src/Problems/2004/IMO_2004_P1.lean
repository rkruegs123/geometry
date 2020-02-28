import Geo.Geo.Core

namespace Geo

open Angle Seg Triangle

def IMO_2004_P1 : Prop :=
∀ (A B C M N R : Point),
acute ⟨A, B, C⟩ →
¬cong ⟨A, B⟩ ⟨A, C⟩ →
intersectAt (Circle.buildDiam (Seg.mk B C)) (Seg.mk A B) M →
intersectAt (Circle.buildDiam (Seg.mk B C)) (Seg.mk A C) N →
let O := (Seg.mk B C).midp;
intersectAt (bisector ⟨B, A, C⟩) (bisector ⟨M, O, N⟩) R →
allIntersect₂ [circumcircle ⟨B, M, R⟩, circumcircle ⟨C, N, R⟩] [Seg.mk B C]

end Geo
