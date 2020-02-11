import Geo.Geo.Core

namespace Geo

open Quadrilateral

def IMO_2016_P1 : Prop :=
∀ (A B C D E F X : Point),
Angle.isRight (Triangle.mk B C F).angles.A → -- Triangle B C F has a right angle at B
on A (Line.mk C F) →
cong (Seg.mk F A) (Seg.mk F B) →
on F (Seg.mk A C) →
cong (Seg.mk D A) (Seg.mk D C) →
Line.same ⟨A, C⟩ (Angle.bisector ⟨D, A, B⟩) →
cong (Seg.mk E A) (Seg.mk E D) →
Line.same ⟨A, D⟩ (Angle.bisector ⟨E, A, C⟩) →
let M := midp (Seg.mk C F);
parallelogram (Quadrilateral.mk A M X E) →
allIntersect [(Line.mk B D), (Line.mk F X), (Line.mk M E)]

end Geo
