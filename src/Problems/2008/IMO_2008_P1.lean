import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2008_P1 : Prop :=
∀ (A B C : Point),
acute ⟨A, B, C⟩ →
let H := orthocenter ⟨A, B, C⟩;
∀ (A₁ A₂ B₁ B₂ C₁ C₂ : Point),
intersectAt₂ (Circle.buildOP (Seg.mk B C).midp H) (Line.mk B C) A₁ A₂ →
intersectAt₂ (Circle.buildOP (Seg.mk C A).midp H) (Line.mk C A) B₁ B₂ →
intersectAt₂ (Circle.buildOP (Seg.mk A B).midp H) (Line.mk A B) C₁ C₂ →
cycl [A₁, A₂, B₁, B₂, C₁, C₂]

end Geo
