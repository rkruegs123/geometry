import Geo.Geo.Core

namespace Geo

open Quadrilateral Seg Triangle

def IMO_2008_P6 : Prop :=
∀ (A B C D : Point),
convex ⟨A, B, C, D⟩ →
¬cong ⟨B, A⟩ ⟨B, C⟩ →
let ω₁ := incircle ⟨A, B, C⟩;
let ω₂ := incircle ⟨A, D, C⟩;
∀ (ω : Circle),
tangent ω (Ray.buildBeyond B A) →
tangent ω (Ray.buildBeyond B C) →
tangent ω (Line.mk A D) →
tangent ω (Line.mk C D) -- → -- could easily clean up

/-
FIXME:

"Prove that the common external tangents of ω₁ and ω₂ intersect on  ω"

Previously, we had the following:
allIntersect₂ (Circle.commonExtTangents ω₁ ω₂) [ω]

We decided that returning a list is not ideal, and to revisit this later
-/

--ryankrue: why doesn't WIP or sorry work here?

end Geo
