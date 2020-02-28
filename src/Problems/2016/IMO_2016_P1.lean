import Geo.Geo.Core

namespace Geo

open Angle Quadrilateral Seg

def IMO_2016_P1 : Prop :=
∀ (A B C D E F X : Point),
Angle.isRight (Triangle.mk B C F).angles.A → -- Triangle B C F has a right angle at B
on A (Line.mk C F) →
cong ⟨F, A⟩ ⟨F, B⟩ →
on F (Seg.mk A C) →
cong ⟨D, A⟩ ⟨D, C⟩ →
isBisector ⟨A, C⟩ ⟨D, A, B⟩ →
cong ⟨E, A⟩ ⟨E, D⟩ →
isBisector ⟨A, D⟩ ⟨E, A, C⟩ →
let M := (Seg.mk C F).midp;
parallelogram (Quadrilateral.mk A M X E) →
Line.concur [(Line.mk B D), (Line.mk F X), (Line.mk M E)]

end Geo
