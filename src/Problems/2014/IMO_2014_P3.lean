import Geo.Geo.Core

namespace Geo

open Triangle
open Quadrilateral
open Angle

def IMO_2014_P3 : Prop :=
∀ (A B C D S T : Point),
convex ⟨A, B, C, D⟩ →
Angle.isRight ⟨A, B, C⟩ →
Angle.isRight ⟨C, D, A⟩ →
let H := foot A (Seg.mk B D);
on S (Seg.mk A B) →
on T (Seg.mk A D) →
inside H (Triangle.mk S C T) →
uangle ⟨C, H, S⟩  - uangle ⟨C, S, B⟩ = Quot.mk RealMod2πEquivalence (π / 2) → -- CHS - CSB is right angle
uangle ⟨T, H, C⟩ - uangle ⟨D, T, C⟩ = Quot.mk RealMod2πEquivalence (π / 2) → -- THC - DTC is right angle
tangent (Line.mk B D) (circumcircle ⟨T, S, H⟩)

end Geo
