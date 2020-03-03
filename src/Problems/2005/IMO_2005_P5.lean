import Geo.Geo.Core

namespace Geo

open Quadrilateral Seg Triangle

def IMO_2005_P5 : Prop :=
∀ (A B C D : Point),
convex ⟨A, B, C, D⟩ →
cong ⟨B, C⟩ ⟨D, A⟩ →
¬para  ⟨B, C⟩ ⟨D, A⟩ →
Exists (λ (X : Point) =>
∀ (E F P Q R : Point),
on E (Seg.mk B C) →
on F (Seg.mk D A) →
cong ⟨B, E⟩ ⟨D, F⟩ →
intersectAt (Line.mk A C) (Line.mk B D) P →
intersectAt (Line.mk B D) (Line.mk E F) Q →
intersectAt (Line.mk E F) (Line.mk A C) R →
X ≠ P → -- ryankrue: may want Point.distinct depending on how NDGs are handled
on X (circumcircle ⟨P, Q, R⟩)
)
end Geo
