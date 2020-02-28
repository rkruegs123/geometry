import Geo.Geo.Core

namespace Geo

open Triangle
open Seg

def IMO_2009_P1 : Prop :=
∀ (A B C P Q : Point),
let O := circumcenter ⟨A, B, C⟩;
on P (Seg.mk C A) →
on Q (Seg.mk A B) →
let K := midp (Seg.mk B P);
let L := midp (Seg.mk C Q);
let M := midp (Seg.mk P Q);
let Γ := Circle.buildPPP K L M;
tangent (Line.mk P Q) Γ →
cong ⟨O, P⟩ ⟨O, Q⟩

end Geo
