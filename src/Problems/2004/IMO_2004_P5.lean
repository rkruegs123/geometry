import Geo.Geo.Core

namespace Geo

open Angle Quadrilateral Seg

def IMO_2004_P5 : Prop :=
∀ (A B C D : Point),
convex ⟨A, B, C, D⟩ →
¬isBisector ⟨B, D⟩ ⟨A, B, C⟩ →
¬isBisector ⟨B, D⟩ ⟨C, D, A⟩ →
∀ (P : Point),
inside P (Quadrilateral.mk A B C D) →
uangle ⟨P, B, C⟩ = uangle ⟨D, B, A⟩ →
uangle ⟨P, D, C⟩ = uangle ⟨B, D, A⟩ →
cyclic ⟨A, B, C, D⟩ ↔ cong ⟨A, P⟩ ⟨C, P⟩

end Geo
