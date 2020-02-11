import Geo.Geo.Core

namespace Geo

def IMO_2001_P5 : Prop :=
∀ (A B C P Q : Point),
on P (Seg.mk B C) →
Line.same ⟨A, P⟩ (Angle.bisector ⟨B, A, C⟩) →
on Q (Seg.mk C A) →
Line.same ⟨B, Q⟩ (Angle.bisector ⟨A, B, C⟩) →
Angle.uangle ⟨B, A, C⟩ = Quot.mk RealMod2πEquivalence (π / 3) →
ulen (Seg.mk A B) + ulen (Seg.mk B P) = ulen (Seg.mk A Q) + ulen (Seg.mk Q B) →
Angle.uangle ⟨C, B, A⟩ = Quot.mk RealMod2πEquivalence (Analytic.degToRadians 80) →
Angle.uangle ⟨A, C, B⟩ = Quot.mk RealMod2πEquivalence (Analytic.degToRadians 40)

end Geo
