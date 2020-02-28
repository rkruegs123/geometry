import Geo.Geo.Core

namespace Geo

open Angle Triangle

def IMO_2010_P2 : Prop :=
∀ (A B C D E F G : Point),
let I := incenter ⟨A, B, C⟩;
let Γ := circumcircle ⟨A, B, C⟩;
intersectAt₂ (Line.mk A I) Γ A D →
on E (Arc.mk Γ B C A) → -- ryankrue: note the utility of the avoid construction here
on F (Seg.mk B C) →
uangle ⟨B, A, F⟩ = uangle ⟨C, A, E⟩ →
uangle ⟨C, A, E⟩ < (1 / 2) * uangle ⟨B, A, C⟩ →
G = (Seg.mk I F).midp → -- ryankrue: use let here? 0 df
allIntersect₂ [Line.mk D G, Line.mk E I] [Γ]


end Geo
