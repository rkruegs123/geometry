import Geo.Geo.Core

namespace Geo

open Geo.Triangle
open Geo.Quadrilateral

def IMO_2018_P6 : Prop :=
∀ (A B C D X : Point),
let q : Quadrilateral := ⟨A, B, C, D⟩;
convex q →
ulen (Seg.mk A B) * ulen (Seg.mk C D) = ulen (Seg.mk B C) * ulen (Seg.mk D A) →
inside X q → -- Note: because HasInside is a class, ⟨A, B, C, D⟩ does not work here
uangle ⟨X, A, B⟩ = uangle ⟨X, C, D⟩ →
uangle ⟨X, B, C⟩ = uangle ⟨X, D, A⟩ →
uangle ⟨B, X, A⟩ + uangle ⟨D, X, C⟩ = π

end Geo
