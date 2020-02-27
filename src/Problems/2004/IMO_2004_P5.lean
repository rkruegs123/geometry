import Geo.Geo.Core

namespace Geo

open Quadrilateral
open Angle

def IMO_2004_P5 : Prop :=
∀ (A B C D P : Point),
convex ⟨A, B, C, D⟩ →
¬isBisector ⟨B, D⟩ ⟨A, B, C⟩ →
¬isBisector ⟨B, D⟩ ⟨C, D, A⟩ →
inside P (Quadrilateral.mk A B C D) →
uangle ⟨P, B, C⟩ = uangle ⟨D, B, A⟩ →
uangle ⟨P, D, C⟩ = uangle ⟨B, D, A⟩ →
cyclic ⟨A, B, C, D⟩ ↔ Seg.cong ⟨A, P⟩ ⟨C, P⟩

end Geo
