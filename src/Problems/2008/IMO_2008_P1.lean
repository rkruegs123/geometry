import Geo.Geo.Core

namespace Geo

open Geo.Triangle

def IMO_2008_P1 : Prop :=
∀ (A A₁ A₂ B B₁ B₂ C C₁ C₂ : Point),
acute ⟨A, B, C⟩ →
let H := orthocenter ⟨A, B, C⟩;
intersectAtt₂ (Circle.buildOP (midp (Seg.mk B C)) H) (Line.mk B C) A₁ A₂ →
intersectAtt₂ (Circle.buildOP (midp (Seg.mk C A)) H) (Line.mk C A) B₁ B₂ →
intersectAtt₂ (Circle.buildOP (midp (Seg.mk A B)) H) (Line.mk A B) C₁ C₂ →
cycl [A₁, A₂, B₁, B₂, C₁, C₂]

end Geo
