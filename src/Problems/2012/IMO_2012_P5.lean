import Geo.Geo.Core

namespace Geo

open Analytic Seg Triangle

def IMO_2012_P5 : Prop :=
∀ (A B C : Point),
deg2π 90 = uangle ⟨B, C, A⟩ →
let D := (altitudes ⟨A, B, C⟩).C.dst;
∀ (K L M X : Point),
on X (Seg.mk C D) →
on K (Seg.mk A X) →
cong ⟨B, K⟩ ⟨B, C⟩ →
on L (Seg.mk B X) →
cong ⟨A, L⟩ ⟨A, C⟩ →
intersectAt (Seg.mk A L) (Seg.mk B K) M →
cong ⟨M, K⟩ ⟨M, L⟩

end Geo
