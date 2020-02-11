import Geo.Geo.Core

namespace Geo

def IMO_2012_P5 : Prop :=
∀ (A B C K L M X : Point),
Angle.uangle ⟨B, C, A⟩ = Quot.mk RealMod2πEquivalence (π / 2) →
let D := foot C ⟨A, B⟩;
on X (Seg.mk C D) →
on K (Seg.mk A X) →
cong (Seg.mk B K) (Seg.mk B C) →
on L (Seg.mk B X) →
cong (Seg.mk A L) (Seg.mk A C) →
intersectAt (Seg.mk A L) (Seg.mk B K) M →
cong (Seg.mk M K) (Seg.mk M L)

end Geo
