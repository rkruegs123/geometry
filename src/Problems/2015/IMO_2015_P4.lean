import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2015_P4 : Prop :=
∀ (A B C D E F G K L X : Point) (Γ : Circle),
let Ω := circumcircle ⟨A, B, C⟩;
let O := circumcenter ⟨A, B, C⟩;
Circle.isOrigin A Γ →
intersectAt₂ Γ (Seg.mk B C) D E →
inOrderOn [B, D, E, C] (Line.mk B C) →
intersectAt₂ Γ Ω F G →
inOrderOn [A, F, B, C, G] Ω →
intersectAt₂ (circumcircle ⟨B, D, F⟩) (Seg.mk A B) B K →
intersectAt₂ (circumcircle ⟨C, G, E⟩) (Seg.mk C A) C L →
intersectAt (Line.mk F K) (Line.mk G L) X →
on X (Line.mk A O)

end Geo
