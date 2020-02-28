import Geo.Geo.Core

namespace Geo

open Analytic Arc Circle Triangle

def IMO_2002_P2 : Prop :=
∀ (A B C E F J O : Point) (Γ : Circle),
isOrigin O Γ →
allOn [A, B, C, E, F] Γ →
isDiameter B C Γ → -- ryankrue: note there is isDiameter₂ for reordering
degToRadians 60 < uangle ⟨A, O, C⟩ →
Line.same (Line.mk E F) (perpBis ⟨A, O⟩) →
let D := (buildMinor Γ A B).midp;
intersectAt (Line.buildPara O ⟨A, D⟩) (Line.mk A C) J →
isIncenter J ⟨C, E, F⟩

end Geo
