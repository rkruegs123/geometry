import Geo.Geo.Core

namespace Geo

open Polygon Triangle

def IMO_2005_P1 : Prop :=
∀ (A A₁ A₂ B B₁ B₂ C C₁ C₂ : Point),
equilateral ⟨A, B, C⟩ →
allOn [A₁, A₂] (Seg.mk B C) →
allOn [B₁, B₂] (Seg.mk C A) →
allOn [C₁, C₂] (Seg.mk A B) →
convex (Polygon.buildPs [A₁, A₂, B₁, B₂, C₁, C₂]) →
(Polygon.buildPs [A₁, A₂, B₁, B₂, C₁, C₂]).equalSides →
Line.concur [⟨A₁, B₂⟩, ⟨B₁, C₂⟩, ⟨C₁, A₂⟩]

end Geo
