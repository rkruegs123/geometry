import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2013_P3 : Prop :=
∀ (A B C A₁ B₁ C₁ : Point),
tangentAt (excircles ⟨A, B, C⟩).A (Seg.mk B C) A₁ →
tangentAt (excircles ⟨A, B, C⟩).B (Seg.mk A C) B₁ →
tangentAt (excircles ⟨A, B, C⟩).C (Seg.mk A B) C₁ →
on (circumcenter ⟨A₁, B₁, C₁⟩) (circumcircle ⟨A, B, C⟩) →
Triangle.isRight ⟨A, B, C⟩

end Geo
