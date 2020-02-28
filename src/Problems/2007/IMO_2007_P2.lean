import Geo.Geo.Core

namespace Geo

open Quadrilateral Seg

def IMO_2007_P2 : Prop :=
∀ (A B C D E F G : Point) (l : Line),
parallelogram ⟨A, B, C, D⟩ →
cyclic ⟨B, C, E, D⟩ →
on A l →
intersectAt l (Seg.mk D C) F →
intersectAt l (Line.mk B C) G →
cong ⟨E, F⟩ ⟨E, G⟩ → 
cong ⟨E, F⟩ ⟨E, C⟩ → -- could make the above two simpler -- both a function that takes in two segments and checks that they are the same length, as well as one that can take in an arbitrary list of segments
Angle.isBisector l ⟨D, A, B⟩


end Geo
