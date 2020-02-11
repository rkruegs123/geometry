import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2015_P4 : Prop :=
∀ (A B C D E F G K L O X : Point),
let Ω := circumcircle ⟨A, B, C⟩;
O = circumcenter ⟨A, B, C⟩ →
let Γ := Circle.mk A (ulen (Seg.mk A D)); -- ryankrue: note how we give the circle radius
intersectAt Γ (Seg.mk B C) D →
intersectAt Γ (Seg.mk B C) E →
inOrderOn [B, D, E, C] (Line.mk B C) →
intersectAt Γ Ω F →
intersectAt Γ Ω G → -- ryankrue: note how again, we do this twice -- could intersectAt take a list of points (and this list could only contain one element if it needed to)?
inOrderOn [A, F, B, C, G] Ω →
intersectAt₂ (circumcircle ⟨B, D, F⟩) (Seg.mk A B) K B →
-- ryankrue: the above has 0 df, so could instead do the following:
-- let K := (intersectionPoints (circumcircle ⟨B, D, F⟩) (Seg.mk A B)).getLast!; -- "Let K be the 2nd point of intersection of the circumcircle of triangle BDF and the segment AB"
intersectAt₂ (circumcircle ⟨C, G, E⟩) (Seg.mk C A) L C →
-- ryankrue: same comment for L as for K
intersectAt (Line.mk F K) (Line.mk G L) X →
on X (Line.mk A O)

end Geo
