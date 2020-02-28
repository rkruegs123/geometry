import Geo.Geo.Core

namespace Geo

open Analytic Angle Quadrilateral Triangle

def IMO_2014_P3 : Prop :=
∀ (A B C D S T : Point),
convex ⟨A, B, C, D⟩ →
Angle.isRight ⟨A, B, C⟩ →
Angle.isRight ⟨C, D, A⟩ →
let H := foot A ⟨B, D⟩;
on S (Seg.mk A B) →
on T (Seg.mk A D) →
inside H (Triangle.mk S C T) →
degToRadians 90 = uangle ⟨C, H, S⟩  - uangle ⟨C, S, B⟩ →
degToRadians 90 = uangle ⟨T, H, C⟩ - uangle ⟨D, T, C⟩ →
tangent (Line.mk B D) (circumcircle ⟨T, S, H⟩)

end Geo
