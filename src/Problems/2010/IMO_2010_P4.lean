import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2010_P4 : Prop :=
∀ (A B C K L M P S : Point),
inside P (Triangle.mk A B C) →
let Γ := circumcircle ⟨A, B, C⟩;
intersectAt Γ (Line.mk A P) K →
intersectAt Γ (Line.mk B P) L →
intersectAt Γ (Line.mk C P) M →
intersectAt (Circle.lineTangentAtP Γ C) (Line.mk A B) S →
Line.same ⟨S, C⟩ ⟨S, P⟩ →
Line.same ⟨M, K⟩ ⟨M, L⟩

end Geo
