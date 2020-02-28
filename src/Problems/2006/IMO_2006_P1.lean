import Geo.Geo.Core

namespace Geo

open Seg Triangle

def IMO_2006_P1 : Prop :=
∀ (A B C P : Point),
let I := incenter ⟨A, B, C⟩;
inside P (Triangle.mk A B C) →
uangle ⟨P, B, A⟩ + uangle ⟨P, C, A⟩ = uangle ⟨P, B, C⟩ + uangle ⟨P, C, B⟩ →
ulen (Seg.mk A P) ≥ ulen (Seg.mk A I) →
cong ⟨A, P⟩ ⟨A, I⟩ ↔ P = I

end Geo
