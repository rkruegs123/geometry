import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2015_P3 : Prop :=
∀ (A B C : Point),
acute ⟨A, B, C⟩ →
ulen (Seg.mk A B) > ulen (Seg.mk A C) →
let Γ := Triangle.circumcircle ⟨A, B, C⟩;
let H := orthocenter ⟨A, B, C⟩;
let F := (altitudes ⟨A, B, C⟩).A.dst; -- is the same as foot A ⟨B, C⟩
let M := (Seg.mk B C).midp;
/-
Note that in the problem statement, K and Q have 0 df.
The function that would have to be introduced to reflect this would be a bit awkward.
-/
∀ (K Q : Point),
on Q Γ →
Angle.isRight ⟨H, Q, A⟩ →
on K Γ →
Angle.isRight ⟨H, K, Q⟩ →
[A, B, C, K, Q].allDistinct →
inOrderOn [A, B, C, K, Q] Γ →
tangent (Triangle.circumcircle ⟨K, Q, H⟩) (Triangle.circumcircle ⟨F, K, M⟩)

end Geo
