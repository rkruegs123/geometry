import Geo.Geo.Core

namespace Geo

open Quadrilateral
open Angle

def IMO_2003_P4 : Prop :=
∀ (A B C D : Point),
cyclic ⟨A, B, C, D⟩ →
let P := foot D ⟨A, B⟩;
let Q := foot D ⟨B, C⟩;
let R := foot D ⟨C, A⟩;
allIntersect [bisector ⟨A, B, C⟩, bisector ⟨C, D, A⟩, Line.mk A C] ↔ Seg.cong ⟨R, P⟩ ⟨R, Q⟩

end Geo
