import Geo.Geo.Core

namespace Geo

open Seg Triangle

def IMO_2019_P6 : Prop :=
∀ (A B C D E F R P Q : Point),
acute ⟨A, B, C⟩ →
¬cong ⟨A, B⟩ ⟨A, C⟩ →
let I := incenter ⟨A, B, C⟩;
let ω := incircle ⟨A, B, C⟩;
tangentAt ω (Seg.mk B C) D →
tangentAt ω (Seg.mk C A) E →
tangentAt ω (Seg.mk A B) F →
intersectAt₂ (Line.mk D (foot D ⟨E, F⟩)) ω R D →
intersectAt₂ (Line.mk A R) ω P R →
intersectAt₂ (circumcircle ⟨P, C, E⟩) (circumcircle ⟨P, B, F⟩) Q P →
allIntersect [Line.mk D I, Line.mk P Q, Line.mk A (perpTo A I)]

end Geo
