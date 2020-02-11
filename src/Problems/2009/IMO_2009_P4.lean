import Geo.Geo.Core

namespace Geo

open Triangle
open Angle

def IMO_2009_P4 : Prop :=
∀ (A B C D E : Point),
cong (Seg.mk A B) (Seg.mk A C) →
intersectAt (Angle.bisector ⟨C, A, B⟩) (Seg.mk B C) D →
intersectAt (Angle.bisector ⟨A, B, C⟩) (Seg.mk C A) E →
let K := incenter ⟨A, D, C⟩;
uangle ⟨B, E, K⟩ = Quot.mk RealMod2πEquivalence (π / 4) →
uangle ⟨C, A, B⟩ = Quot.mk RealMod2πEquivalence (π / 3) ∨ uangle ⟨C, A, B⟩ = Quot.mk RealMod2πEquivalence (π / 2)

end Geo
