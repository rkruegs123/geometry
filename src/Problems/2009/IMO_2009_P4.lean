import Geo.Geo.Core

namespace Geo

open Triangle
open Angle
open Seg

def IMO_2009_P4 : Prop :=
∀ (A B C D E : Point),
cong ⟨A, B⟩ ⟨A, C⟩ →
intersectAt (Angle.bisector ⟨C, A, B⟩) (Seg.mk B C) D →
intersectAt (Angle.bisector ⟨A, B, C⟩) (Seg.mk C A) E →
let K := incenter ⟨A, D, C⟩;
Analytic.degToRadians 45 = uangle ⟨B, E, K⟩ →
Analytic.degToRadians 60 = uangle ⟨C, A, B⟩ ∨ Analytic.degToRadians 90 = uangle ⟨C, A, B⟩

end Geo
