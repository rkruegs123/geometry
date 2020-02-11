import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2011_P6 : Prop :=
∀ (A B C : Point) (l : Line),
acute ⟨A, B, C⟩ →
let Γ := circumcircle ⟨A, B, C⟩;
tangent l Γ →
let la := reflect l (Line.mk B C);
let lb := reflect l (Line.mk C A); -- ryankrue: why can I subscript a (i.e., lₐ) but not b?
let lc := reflect l (Line.mk A B);
tangent Γ $ circumcircle (Triangle.buildLLL la lb lc)

end Geo
