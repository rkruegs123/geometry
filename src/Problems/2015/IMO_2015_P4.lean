import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2015_P4 : Prop :=
∀ (A B C D E F G K L O X : Point) (Γ : Circle),
let Ω := circumcircle ⟨A, B, C⟩;
O = circumcenter ⟨A, B, C⟩ →
A = Γ.origin →
intersectAtt₂ Γ (Seg.mk B C) D E →
inOrderOn [B, D, E, C] (Line.mk B C) →
intersectAtt₂ Γ Ω F G →
inOrderOn [A, F, B, C, G] Ω →
intersectAtt₂ (circumcircle ⟨B, D, F⟩) (Seg.mk A B) B K →
intersectAtt₂ (circumcircle ⟨C, G, E⟩) (Seg.mk C A) C L →
intersectAt (Line.mk F K) (Line.mk G L) X →
on X (Line.mk A O)

end Geo
