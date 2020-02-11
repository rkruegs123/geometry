import Geo.Geo.Core

namespace Geo

open Geo.Triangle

def IMO_2018_P1 : Prop :=
∀ (A B C D E F G : Point),
acute ⟨A, B, C⟩ →
let Γ := circumcircle ⟨A, B, C⟩;
on D (Seg.mk A B) →
on E (Seg.mk A C) →
cong (Seg.mk A D) (Seg.mk A E) →
intersectAt (perpBis ⟨B, D⟩) (Arc.buildMinor Γ A B) F →
intersectAt (perpBis ⟨C, E⟩) (Arc.buildMinor Γ A C) G →
para ⟨D, E⟩ ⟨F, G⟩ ∨ Line.same ⟨D, E⟩ ⟨F, G⟩ -- (depends on how we define para)

end Geo
