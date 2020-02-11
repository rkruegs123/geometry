import Geo.Geo.Core

namespace Geo

open Triangle
open WithInst

def IMO_2004_P1 : Prop :=
∀ (A B C M N R : Point),
acute ⟨A, B, C⟩ →
¬cong (Seg.mk B C) (Seg.mk A C) →
intersectAt (Circle.buildDiam (Seg.mk B C)) (Seg.mk A B) M →
intersectAt (Circle.buildDiam (Seg.mk B C)) (Seg.mk A C) N →
let O := midp (Seg.mk B C);
intersectAt (Angle.bisector ⟨B, A, C⟩) (Angle.bisector ⟨M, O, N⟩) R →
allIntersect₂ [intersectElem $ circumcircle ⟨B, M, R⟩, intersectElem $ circumcircle ⟨C, N, R⟩, intersectElem $ Seg.mk B C]

end Geo
