import Geo.Geo.Core

namespace Geo

open Geo.Triangle

def IMO_2018_P1 : Prop :=
∀ (A B C D E F G : Point),
acute ⟨A, B, C⟩ →
let Γ := circumcircle ⟨A, B, C⟩;
on D (Seg.mk A B) →
on E (Seg.mk A C) →
ulen (Seg.mk A D) = ulen (Seg.mk A E) → -- looks ugly, cong is nicer, or notation
intersectAt (perpBis ⟨B, D⟩) (Arc.mk Γ A B C) F →
intersectAt (perpBis ⟨C, E⟩) (Arc.mk Γ C A B) G →
para ⟨D, E⟩ ⟨F, G⟩ ∨ Line.mk D E = Line.mk F G -- (depends on how we define para)

end Geo
