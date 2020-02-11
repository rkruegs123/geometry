import Geo.Geo.Core

namespace Geo

def IMO_2015_P4 : Prop :=
∀ (A B C : Point),
let Ω := Triangle.circumcircle ⟨A, B, C⟩;
let O := Triangle.circumcenter ⟨A, B, C⟩;
∀ (D E : Point) (Γ : Circle),
Circle.isOrigin A Γ →
intersectAt₂ Γ (Seg.mk B C) D E →
[B, D, E, C].allDistinct →
inOrderOn [B, D, E, C] (Line.mk B C) →
∀ (F G : Point),
intersectAt₂ Γ Ω F G →
inOrderOn [A, F, B, C, G] Ω →
∀ (K L : Point),
intersectAt₂ (Triangle.circumcircle ⟨B, D, F⟩) (Seg.mk A B) B K →
intersectAt₂ (Triangle.circumcircle ⟨C, G, E⟩) (Seg.mk C A) C L →
¬Line.same ⟨F, K⟩ ⟨G, L⟩ →
∀ (X : Point),
intersectAt (Line.mk F K) (Line.mk G L) X →
on X (Line.mk A O)

end Geo
