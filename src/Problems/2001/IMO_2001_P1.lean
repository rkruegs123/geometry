import Geo.Geo.Core

namespace Geo

open Geo.Triangle
open Geo.Angle

def IMO_2001_P1 : Prop :=
∀ (A B C : Point),
acute ⟨A, B, C⟩ →
let O := circumcenter ⟨A, B, C⟩;
let P := foot A ⟨B, C⟩;
uangle ⟨B, C, A⟩ ≥ uangle ⟨A, B, C⟩ + Quot.mk RealMod2πEquivalence (Analytic.degToRadians 30) → -- BCA >= ABC + 30
uangle ⟨C, A, B⟩ + uangle ⟨C, O, P⟩ < Quot.mk RealMod2πEquivalence (π / 2) -- CAB + COP < 90

end Geo
