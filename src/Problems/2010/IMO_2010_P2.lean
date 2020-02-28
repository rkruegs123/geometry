import Geo.Geo.Core

namespace Geo

open Triangle
open Angle

def IMO_2010_P2 : Prop :=
∀ (A B C D E F G : Point),
let I := incenter ⟨A, B, C⟩;
let Γ := circumcircle ⟨A, B, C⟩;
intersectAtt₂ (Line.mk A I) Γ A D →
on E (Arc.mk Γ B C A) → -- ryankrue: note the utility of the avoid construction here
on F (Seg.mk B C) →
uangle ⟨B, A, F⟩ = uangle ⟨C, A, E⟩ →
uangle ⟨C, A, E⟩ < (1 / 2) * uangle ⟨B, A, C⟩ →
G = midp (Seg.mk I F) → -- ryankrue: use let here? 0 df
allIntersect₂ [Line.mk D G, Line.mk E I] [Γ]


end Geo
