import Geo.Geo.Core

namespace Geo

open Quadrilateral
open Triangle
open WithInst

def IMO_2006_P6 : Prop :=
∀ (A B C D : Point) (ω : Circle),
convex ⟨A, B, C, D⟩ →
ulen (Seg.mk B A) ≠ ulen (Seg.mk B C) →
let ω₁ := incircle ⟨A, B, C⟩;
let ω₂ := incircle ⟨A, D, C⟩;
tangent ω (Ray.mk B A) →
tangent ω (Ray.mk B C) →
tangent ω (Line.mk A D) →
tangent ω (Line.mk C D) → -- could easily clean up
allIntersect₂ ((Circle.commonExtTangents ω₁ ω₂).map (λ l => intersectElem l)) -- the common external tangents of ω₁ and ω₂ intersect on ω

end Geo
