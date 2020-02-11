import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2007_P4 : Prop :=
∀ (A B C P Q R : Point),
intersectAt (Angle.bisector ⟨B, C, A⟩) (circumcircle ⟨A, B, C⟩) R →
intersectAt (Angle.bisector ⟨B, C, A⟩) (perpBis (Seg.mk B C)) P →
intersectAt (Angle.bisector ⟨B, C, A⟩) (perpBis (Seg.mk A C)) Q →
let K := midp (Seg.mk B C);
let L := midp (Seg.mk A C);
(Triangle.mk R P K).uarea = (Triangle.mk R Q L).uarea

end Geo
