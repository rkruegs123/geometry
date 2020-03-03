import Geo.Geo.Core

namespace Geo

open Angle Quadrilateral Seg

def IMO_2016_P1 : Prop :=
∀ (B C F : Point),
Angle.isRight (Triangle.mk B C F).angles.A → -- Triangle B C F has a right angle at B
∀ (A D E: Point),
on A (Line.mk C F) →
cong ⟨F, A⟩ ⟨F, B⟩ →
on F (Seg.mk A C) →
cong ⟨D, A⟩ ⟨D, C⟩ →
isBisector ⟨A, C⟩ ⟨D, A, B⟩ →
cong ⟨E, A⟩ ⟨E, D⟩ →
isBisector ⟨A, D⟩ ⟨E, A, C⟩ →
let M := (Seg.mk C F).midp;
∀ (X : Point),
parallelogram (Quadrilateral.mk A M X E) →
Line.concur [⟨B, D⟩, ⟨F, X⟩, ⟨M, E⟩]

end Geo
