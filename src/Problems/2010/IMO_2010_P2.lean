import Geo.Geo.Core

namespace Geo

open Triangle
open Angle
open WithInst

def IMO_2010_P2 : Prop :=
∀ (A B C D E F G : Point),
let I := incenter ⟨A, B, C⟩;
let Γ := circumcircle ⟨A, B, C⟩;
intersectAt (Line.mk A I) Γ D →
on E (Arc.mk Γ B C A) → -- ryankrue: note the utility of the avoid construction here
on F (Seg.mk B C) →
uangle ⟨B, A, F⟩ = uangle ⟨C, A, E⟩ →
uangle ⟨C, A, E⟩ < (Quot.mk RealMod2πEquivalence (1 / 2)) * uangle ⟨B, A, C⟩ → -- ryankrue: could just have HasDiv for Real2π. Note that if we have HasDiv for Real2π, we may not even have to do Quot.mk when we want to do things like: some angle = π / 4 (Real2π would also have to have HasPi)
midp (Seg.mk I F) = G → -- ryankrue: use let here? 0 df
allIntersect₂ [intersectElem $ Line.mk D G, intersectElem $ Line.mk E I, intersectElem Γ]

end Geo
