import Geo.Geo.Core

namespace Geo

open Geo.Triangle


def IMO_2016_P2 : Prop :=
∀ (A B C D E F M I P X : Point),
acute ⟨A, B, C⟩ → 
incenter ⟨A, B, C⟩ = I → -- I is the incenter of the triangle
midp (Seg.mk B C) = M → --M is midpoint of BC
foot I ⟨B, C⟩ = D → -- D is the foot of perpendicular from I to BC
perp ⟨I, P⟩ ⟨A, I⟩ → -- note that we could alternatively do the following:
-- assume (P : Point);
-- assume perp ⟨I, P⟩ ⟨A, I⟩;
intersectAt (Line.mk I P) (Line.mk A B) F →
intersectAt (Line.mk I P) (Line.mk A C) E →
let Γ₁ := circumcircle ⟨A, B, C⟩;
let Γ₂ := circumcircle ⟨A, E, F⟩;
intersectAt₂ Γ₁ Γ₂ X A


end Geo
