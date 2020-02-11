import Geo.Geo.Core

namespace Geo

open Seg

def IMO_2019_P2 : Prop :=
∀ (A B C A₁ B₁ : Point),
on A₁ (Seg.mk B C) →
on B₁ (Seg.mk C A) →
∀ (P Q : Point),
on P  (Seg.mk A A₁) →
on Q  (Seg.mk B B₁) →
para ⟨P, Q⟩ ⟨A, B⟩ →
∀ (P₁ Q₁ : Point),
on P₁ (Line.mk P B₁) → -- (strict) alt: coll & bet
strictlyBtw B₁ P P₁ →
uangle ⟨P, P₁, C⟩ = uangle ⟨B, A, C⟩ →
on Q₁ (Line.mk Q A₁) →
strictlyBtw A₁ Q Q₁ →
uangle ⟨C, Q₁, Q⟩ = uangle ⟨C, B, A⟩ →
cycl [P, Q, P₁, Q₁]

end Geo
