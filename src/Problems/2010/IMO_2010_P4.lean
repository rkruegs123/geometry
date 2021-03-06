import Geo.Geo.Core

namespace Geo

open Seg

def IMO_2010_P4 : Prop :=
∀ (A B C P : Point),
inside P (Triangle.mk A B C) →
let Γ := Triangle.circumcircle ⟨A, B, C⟩;
∀ (K L M S : Point),
intersectAt₂ Γ (Line.mk A P) A K →
intersectAt₂ Γ (Line.mk B P) B L →
intersectAt₂ Γ (Line.mk C P) C M →
intersectAt (Circle.lineTangentAtP Γ C) (Line.mk A B) S →
cong ⟨S, C⟩ ⟨S, P⟩ →
cong ⟨M, K⟩ ⟨M, L⟩

end Geo
