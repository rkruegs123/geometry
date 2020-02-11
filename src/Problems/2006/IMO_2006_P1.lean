import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2006_P1 : Prop :=
∀ (A B C P : Point),
let I := incenter ⟨A, B, C⟩;
inside P (Triangle.mk A B C) →
ulen (Seg.mk A P) ≥ ulen (Seg.mk A I) →
cong (Seg.mk A P) (Seg.mk A I) ↔ P = I

end Geo
