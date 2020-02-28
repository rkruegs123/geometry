import Geo.Geo.Core

namespace Geo

open Quadrilateral
open Seg

def IMO_2016_P1 : Prop :=
∀ (A B C D E F X : Point),
Angle.isRight (Triangle.mk B C F).angles.A → -- Triangle B C F has a right angle at B
on A (Line.mk C F) →
cong ⟨F, A⟩ ⟨F, B⟩ →
on F (Seg.mk A C) →
cong ⟨D, A⟩ ⟨D, C⟩ →
Line.same ⟨A, C⟩ (Angle.bisector ⟨D, A, B⟩) →
cong ⟨E, A⟩ ⟨E, D⟩ →
Line.same ⟨A, D⟩ (Angle.bisector ⟨E, A, C⟩) →
let M := midp (Seg.mk C F);
parallelogram (Quadrilateral.mk A M X E) →
allIntersect [(Line.mk B D), (Line.mk F X), (Line.mk M E)]

end Geo
