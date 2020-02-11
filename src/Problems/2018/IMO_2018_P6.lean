import Geo.Geo.Core

namespace Geo

open Geo.Triangle
open Geo.Quadrilateral
open Geo.Angle

def IMO_2018_P6 : Prop :=
∀ (A B C D X : Point),
convex (Quadrilateral.mk A B C D) →
ulen (Seg.mk A B) * ulen (Seg.mk C D) = ulen (Seg.mk B C) * ulen (Seg.mk D A) →
inside X (Quadrilateral.mk A B C D) →
uangle ⟨X, A, B⟩ = uangle ⟨X, C, D⟩ →
uangle ⟨X, B, C⟩ = uangle ⟨X, D, A⟩ →
uangle ⟨B, X, A⟩ + uangle ⟨D, X, C⟩ = π

end Geo
