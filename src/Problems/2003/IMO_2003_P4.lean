import Geo.Geo.Core

namespace Geo

open Quadrilateral
open WithInst

def IMO_2003_P4 : Prop :=
∀ (A B C D : Point),
cyclic ⟨A, B, C, D⟩ →
let P := foot D ⟨A, B⟩;
let Q := foot D ⟨B, C⟩;
let R := foot D ⟨C, A⟩;
allIntersect₂ [intersectElem $ Angle.bisector ⟨A, B, C⟩, intersectElem $ Angle.bisector ⟨C, D, A⟩, intersectElem $ Line.mk A C] ↔ ulen (Seg.mk R P) = ulen (Seg.mk R Q)

end Geo
