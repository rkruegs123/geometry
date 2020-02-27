import Geo.Geo.Core

namespace Geo

open Geo.Triangle
open Geo.Arc

def IMO_2002_P2 : Prop :=
∀ (A B C E F J O : Point) (Γ : Circle),
O = Γ.origin →
allOn Γ [A, B, C, E, F] →
Circle.isDiameter B C Γ → -- ryankrue: note there is isDiameter₂ for reordering
Analytic.degToRadians 60 < uangle ⟨A, O, C⟩ →
Line.same (Line.mk E F) (perpBis ⟨A, O⟩) →
let D := midp (buildMinor Γ A B);
intersectAt (Line.buildPara O ⟨A, D⟩) (Line.mk A C) J →
J = incenter ⟨C, E, F⟩

end Geo
