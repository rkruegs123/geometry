import Geo.Geo.Core

namespace Geo

open Angle Seg Triangle

def IMO_2004_P1 : Prop :=
∀ (A B C : Point),
acute ⟨A, B, C⟩ →
¬cong ⟨A, B⟩ ⟨A, C⟩ →
∀ (M N : Point),
intersectAt (Circle.buildDiam B C) (Seg.mk A B) M →
intersectAt (Circle.buildDiam B C) (Seg.mk A C) N →
let O := (Seg.mk B C).midp;
∀ (R : Point),
intersectAt (bisector ⟨B, A, C⟩) (bisector ⟨M, O, N⟩) R →
allIntersect₂ [Triangle.circumcircle ⟨B, M, R⟩, Triangle.circumcircle ⟨C, N, R⟩] [Seg.mk B C]

end Geo
