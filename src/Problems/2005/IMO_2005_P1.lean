import Geo.Geo.Core

namespace Geo

open Line Polygon Triangle

def IMO_2005_P1 : Prop :=
∀ (A B C : Point),
equilateral ⟨A, B, C⟩ →
∀ (A₁ A₂ B₁ B₂ C₁ C₂ : Point),
allOn [A₁, A₂] (Seg.mk B C) →
allOn [B₁, B₂] (Seg.mk C A) →
allOn [C₁, C₂] (Seg.mk A B) →
convex (Polygon.buildPs [A₁, A₂, B₁, B₂, C₁, C₂]) →
(Polygon.buildPs [A₁, A₂, B₁, B₂, C₁, C₂]).equalSides →
allIntersect [Line.mk A₁ B₂, Line.mk B₁ C₂, Line.mk C₁ A₂]

end Geo
