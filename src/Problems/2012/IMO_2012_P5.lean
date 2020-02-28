import Geo.Geo.Core

namespace Geo

open Analytic Seg

def IMO_2012_P5 : Prop :=
∀ (A B C K L M X : Point),
degToRadians 90 = uangle ⟨B, C, A⟩ →
let D := foot C ⟨A, B⟩; -- FIXME: use the altitude explicitly
on X (Seg.mk C D) →
on K (Seg.mk A X) →
cong ⟨B, K⟩ ⟨B, C⟩ →
on L (Seg.mk B X) →
cong ⟨A, L⟩ ⟨A, C⟩ →
intersectAt (Seg.mk A L) (Seg.mk B K) M →
cong ⟨M, K⟩ ⟨M, L⟩

end Geo
