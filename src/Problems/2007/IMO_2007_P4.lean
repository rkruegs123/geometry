import Geo.Geo.Core

namespace Geo

open Angle Triangle

def IMO_2007_P4 : Prop :=
∀ (A B C P Q R : Point),
intersectAt (bisector ⟨B, C, A⟩) (circumcircle ⟨A, B, C⟩) R →
intersectAt (bisector ⟨B, C, A⟩) (perpBis (Seg.mk B C)) P →
intersectAt (bisector ⟨B, C, A⟩) (perpBis (Seg.mk A C)) Q →
let K := (Seg.mk B C).midp;
let L := (Seg.mk A C).midp;
(Triangle.mk R P K).uarea = (Triangle.mk R Q L).uarea

end Geo
