import Geo.Geo.Core

namespace Geo

open Geo.Triangle

def IMO_2019_P2 : Prop :=
∀ (A B C A₁ B₁ P Q P₁ Q₁ : Point),
on A₁ (Seg.mk B C) →
on B₁ (Seg.mk C A) →
on P  (Seg.mk A A₁) →
on Q  (Seg.mk B B₁) →
para ⟨P, Q⟩ ⟨A, B⟩ →
on B (Seg.mk P P₁) → -- (strict) alt: coll & bet
uangle ⟨P, P₁, C⟩ = uangle ⟨B, A, C⟩ →
on A₁ (Seg.mk Q Q₁) →
uangle ⟨C, Q₁, Q⟩ = uangle ⟨C, B, A⟩ →
cycl [P, Q, P₁, Q₁]

end Geo
