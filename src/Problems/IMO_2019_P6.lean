import Geo.Geo.Core

namespace Geo

open Geo.Triangle

def IMO_2019_P6 : Prop :=
∀ (A B C D E F R P Q : Point),
isAcute ⟨A, B, C⟩ →
ulen (Seg.mk A B) ≠ ulen (Seg.mk A C) →
let I := incenter ⟨A, B, C⟩;
let ω := incircle ⟨A, B, C⟩;
tangentAt ω (Seg.mk B C) D →
tangentAt ω (Seg.mk C A) E →
tangentAt ω (Seg.mk A B) F →
intersectAt (Line.mk D (foot D ⟨E, F⟩)) ω R →
R ≠ D → -- alt: intersectsAt₂
intersectAt (Line.mk A R) ω P →
P ≠ R →
intersectAt (circumcircle ⟨P, C, E⟩) (circumcircle ⟨P, B, F⟩) Q →
Q ≠ P →
allIntersect [Line.mk D I, Line.mk P Q, Line.mk A (perpTo A I)]

end Geo
