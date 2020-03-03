import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2011_P6 : Prop :=
∀ (A B C : Point),
acute ⟨A, B, C⟩ →
let Γ := Triangle.circumcircle ⟨A, B, C⟩;
∀ (l : Line),
tangent l Γ →
let la := reflect l (Line.mk B C);
let lb := reflect l (Line.mk C A);
let lc := reflect l (Line.mk A B);
tangent Γ $ Triangle.circumcircle (Triangle.buildLLL ⟨la, lb, lc⟩)

end Geo
