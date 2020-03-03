import Geo.Geo.Core

namespace Geo

open Analytic Arc Circle Triangle

def IMO_2002_P2 : Prop :=
∀ (B C O : Point) (Γ : Circle),
isOrigin O Γ →
isDiameter B C Γ →
∀ (A : Point),
on A Γ →
degToRadians 60 < uangle ⟨A, O, C⟩ →
∀ (E F : Point),
on E Γ → -- ryankrue: could have isChord (p₁ p₂ : Point) (Γ : Circle)
on F Γ →
isPerpBis ⟨E, F⟩ ⟨A, O⟩ →
let D := (buildMinor Γ A B).midp;
∀ (J : Point),
intersectAt (Line.buildPara O ⟨A, D⟩) (Line.mk A C) J →
isIncenter J ⟨C, E, F⟩

end Geo
