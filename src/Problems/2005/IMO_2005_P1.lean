import Geo.Geo.Core

namespace Geo

open Triangle
open Polygon

def IMO_2005_P1 : Prop :=
∀ (A A₁ A₂ B B₁ B₂ C C₁ C₂ : Point),
equilateral ⟨A, B, C⟩ →
allOn (Seg.mk B C) [A₁, A₂] →
allOn (Seg.mk C A) [B₁, B₂] →
allOn (Seg.mk A B) [C₁, C₂] →
convex (Polygon.buildPs [A₁, A₂, B₁, B₂, C₁, C₂]) →
(Polygon.buildPs [A₁, A₂, B₁, B₂, C₁, C₂]).equalSides →
allIntersect [(Line.mk A₁ B₂), (Line.mk B₁ C₂), (Line.mk C₁ A₂)]

end Geo
