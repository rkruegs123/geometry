import Geo.Geo.Core

namespace Geo

open Angle Quadrilateral Seg

def IMO_2007_P2 : Prop :=
∀ (A B C D E : Point),
parallelogram ⟨A, B, C, D⟩ →
cyclic ⟨B, C, E, D⟩ →
∀ (l : Line),
on A l →
∀ (F G : Point),
intersectAt l (Seg.mk D C) F →
intersectAt l (Line.mk B C) G →
cong ⟨E, F⟩ ⟨E, G⟩ →
cong ⟨E, F⟩ ⟨E, C⟩ →
isBisector l ⟨D, A, B⟩


end Geo
