import Geo.Geo.Core

namespace Geo

open Quadrilateral

def IMO_2004_P5 : Prop :=
∀ (A B C D P : Point),
convex ⟨A, B, C, D⟩ →
¬Line.same (Line.mk B D) (Angle.bisector ⟨A, B, C⟩) → -- ryankrue: is this the best way to denote this?
¬Line.same (Line.mk B D) (Angle.bisector ⟨C, D, A⟩) →
inside P (Quadrilateral.mk A B C D) →
Angle.uangle ⟨P, B, C⟩ = Angle.uangle ⟨D, B, A⟩ →
Angle.uangle ⟨P, D, C⟩ = Angle.uangle ⟨B, D, A⟩ →
cyclic ⟨A, B, C, D⟩ ↔ ulen (Seg.mk A P) = ulen (Seg.mk C P)

end Geo
