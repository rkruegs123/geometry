import Geo.Geo.Core

namespace Geo

open Quadrilateral
open Triangle
open Seg

def IMO_2005_P5 : Prop :=
∀ (A B C D E F P Q R Comm : Point),
convex ⟨A, B, C, D⟩ →
cong ⟨B, C⟩ ⟨D, A⟩ →
¬para  ⟨B, C⟩ ⟨D, A⟩ →
on E (Seg.mk B C) →
on F (Seg.mk D A) →
cong ⟨B, E⟩ ⟨D, F⟩ →
intersectAt (Line.mk A C) (Line.mk B D) P →
intersectAt (Line.mk B D) (Line.mk E F) Q →
intersectAt (Line.mk E F) (Line.mk A C) R →
on Comm (circumcircle ⟨P, Q, R⟩) -- ryankrue: Do you agree this is an accurate way of representing the statement, "prove that the circumcircles of the triangles PQR, as E and F vary, have a common point other than P." I have translated to "there is a point Comm that is always on the circumcircle P Q R when it satisfies the previous predicates with E and F"

end Geo
