import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2012_P1 : Prop :=
∀ (A B C : Point),
let J := (excircles ⟨A, B, C⟩).A.origin;
∀ (K L M : Point),
tangentAt (excircles ⟨A, B, C⟩).A (Seg.mk B C) M → -- note how this is still a Seg
tangentAt (excircles ⟨A, B, C⟩).A (Line.mk A B) K →
tangentAt (excircles ⟨A, B, C⟩).A (Line.mk A C) L →
∀ (F G S T : Point),
intersectAt (Line.mk L M) (Line.mk B J) F →
intersectAt (Line.mk K M) (Line.mk C J) G →
intersectAt (Line.mk A F) (Line.mk B C) S →
intersectAt (Line.mk A G) (Line.mk B C) T →
Seg.isMidpoint M ⟨S, T⟩

end Geo
