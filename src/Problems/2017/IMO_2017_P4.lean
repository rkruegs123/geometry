import Geo.Geo.Core

namespace Geo

open Triangle
open Circle

def IMO_2017_P4 : Prop :=
∀ (A J K R S T : Point) (Ω : Circle),
on R Ω →
on S Ω →
ulen (Seg.mk R S) ≠ Ω.diameter →
let l := lineTangentAtP Ω R;
S = midp (Seg.mk R T) → -- ryankrue: note how we don't use let here
on J (Arc.buildMinor Ω R S) →
let Γ := circumcircle ⟨J, S, T⟩;
2 = numIntersections Γ l →
(intersectionPoints Γ l).allP (λ p => (Geo.Analytic.dist p R) ≥ (Geo.Analytic.dist A R)) → -- ryankrue: could likely do in a simpler way. "let A be the common point of Γ and l that is closer to R." This line translates to "the distance from any intersectoin point to R is no less than the distance from A to R"
intersectAt (Line.mk A J) Ω K →
tangent (Line.mk K T) Γ

end Geo
