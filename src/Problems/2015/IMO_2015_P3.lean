import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2015_P3 : Prop :=
∀ (A B C K Q : Point),
acute ⟨A, B, C⟩ →
ulen (Seg.mk A B) > ulen (Seg.mk A C) →
let H := orthocenter ⟨A, B, C⟩;
let F := foot A (Seg.mk B C);
let M := midp (Seg.mk B C);
let Γ := circumcircle ⟨A, B, C⟩;
on Q Γ →
Angle.isRight ⟨H, Q, A⟩ →
on K Γ →
Angle.isRight ⟨H, K, Q⟩ →
inOrderOn [A, B, C, K] Γ →
tangent (circumcircle ⟨K, Q, H⟩) (circumcircle ⟨F, K, M⟩)

end Geo
