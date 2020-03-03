import Geo.Geo.Core

namespace Geo

open Seg Triangle

def IMO_2018_P1 : Prop :=
∀ (A B C : Point),
acute ⟨A, B, C⟩ →
let Γ := Triangle.circumcircle ⟨A, B, C⟩;
∀ (D E : Point),
on D (Seg.mk A B) →
on E (Seg.mk A C) →
cong ⟨A, D⟩ ⟨A, E⟩ →
∀ (F G : Point),
intersectAt (perpBis ⟨B, D⟩) (Arc.buildMinor Γ A B) F →
intersectAt (perpBis ⟨C, E⟩) (Arc.buildMinor Γ A C) G →
para ⟨D, E⟩ ⟨F, G⟩ ∨ Line.same ⟨D, E⟩ ⟨F, G⟩ -- (depends on how we define para)

end Geo
