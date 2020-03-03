import Geo.Geo.Core

namespace Geo

open Analytic Angle Quadrilateral

def IMO_2014_P3 : Prop :=
∀ (A B C D : Point),
convex ⟨A, B, C, D⟩ →
Angle.isRight ⟨A, B, C⟩ → -- ryankrue: should we use Analytic.degToRadians 90 here?
Angle.isRight ⟨C, D, A⟩ → -- same as above
let H := foot A ⟨B, D⟩;
∀ (S T : Point),
on S (Seg.mk A B) →
on T (Seg.mk A D) →
inside H (Triangle.mk S C T) →
degToRadians 90 = uangle ⟨C, H, S⟩  - uangle ⟨C, S, B⟩ →
degToRadians 90 = uangle ⟨T, H, C⟩ - uangle ⟨D, T, C⟩ →
tangent (Line.mk B D) (Triangle.circumcircle ⟨T, S, H⟩)

end Geo
