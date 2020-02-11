import Geo.Geo.Core

namespace Geo

open Seg Triangle

def IMO_2009_P2 : Prop :=
∀ (A B C P Q : Point),
let O := circumcenter ⟨A, B, C⟩;
on P (Seg.mk C A) →
on Q (Seg.mk A B) →
let K := (Seg.mk B P).midp;
let L := (Seg.mk C Q).midp;
let M := (Seg.mk P Q).midp;
let Γ := Circle.buildPPP K L M;
tangent (Line.mk P Q) Γ →
cong ⟨O, P⟩ ⟨O, Q⟩

end Geo
