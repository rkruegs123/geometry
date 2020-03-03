import Geo.Geo.Core

namespace Geo

open Seg

def IMO_2000_P1 : Prop :=
∀ (A B C D M N : Point),
/-
Deviation from problem statement:

The original problem statement begins with the following:
"AB is tangent to the circles CAMN and NMBD."

We instead check that the quadrilateral is cyclic, and then use its circumcircle.

Note that the implementation of Quadrilateral.cyclic works in the following way:
-Build a circle from 3 points and confirm the 4th point is on that circle

This problem is identical to the Polygon.convex problem
-/
Quadrilateral.cyclic ⟨C, A, M, N⟩ → -- under the hood: on N (Circle.buildPPP C A M)
Quadrilateral.cyclic ⟨N, M, B, D⟩ → -- under the hood: on D (Circle.buildPPP N M B)
-- may be useful to have tangentAtMany predicate
tangent (Line.mk A B) (Quadrilateral.circumcircle ⟨C, A, M, N⟩ WIP) →
tangent (Line.mk A B) (Quadrilateral.circumcircle ⟨N, M, B, D⟩ WIP) →
on M (Seg.mk C D) →
para ⟨C, D⟩ ⟨A, B⟩ →
∀ (E P Q : Point),
intersectAt (Seg.mk N A) (Seg.mk C M) P →
intersectAt (Seg.mk N B) (Seg.mk M D) Q →
intersectAt (Ray.mk C A) (Ray.mk D B) E →
cong ⟨P, E⟩ ⟨Q, E⟩

end Geo
