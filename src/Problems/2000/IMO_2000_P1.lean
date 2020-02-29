import Geo.Geo.Core

namespace Geo

open Seg

def IMO_2000_P1 : Prop :=
∀ (A B C D E M N P Q : Point),
/-
Deviation from problem statement: 

The original problem statement begins with the following:
"AB is tangent to the circles CAMN and NMBD."

Rather than constructing circle from 4 points, we build a circle from 3 points 
and confirm the 4th point is on that circle. In the future, this could be encoded
as a predicate that takes a list of n > 3 points and checks that they all lie on
a circle together by constructing a circle out of the first three and checking
that the remaining points lie on that circle. Still wouldn't align with the text.

This problem is identical to the Polygon.convex problem
-/
on N (Circle.buildPPP C A M) → -- alternatively: Quadrilateral.cyclic ⟨C, A, M, N⟩
on D (Circle.buildPPP N M B) → -- alternatively: Quadrilateral.cyclic ⟨N, M, B, D⟩
-- may be useful to have tangentAtMany predicate
tangent (Line.mk A B) (Circle.buildPPP C A M) →
tangent (Line.mk A B) (Circle.buildPPP N M B) →
strictlyBtw M C D →
para ⟨C, D⟩ ⟨A, B⟩ →
intersectAt (Seg.mk N A) (Seg.mk C M) P →
intersectAt (Seg.mk N B) (Seg.mk M D) Q →
intersectAt (Ray.mk C A) (Ray.mk D B) E →
cong ⟨P, E⟩ ⟨Q, E⟩

end Geo
