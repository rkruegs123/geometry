import Geo.Geo.Core

namespace Geo

open Analytic Angle Quadrilateral Triangle

def IMO_2018_P6 : Prop :=
∀ (A B C D : Point),
convex (Quadrilateral.mk A B C D) →
ulen (Seg.mk A B) * ulen (Seg.mk C D) = ulen (Seg.mk B C) * ulen (Seg.mk D A) →
∀ (X : Point),
inside X (Quadrilateral.mk A B C D) →
uangle ⟨X, A, B⟩ = uangle ⟨X, C, D⟩ →
uangle ⟨X, B, C⟩ = uangle ⟨X, D, A⟩ →
deg2π 180 = uangle ⟨B, X, A⟩ + uangle ⟨D, X, C⟩

end Geo
