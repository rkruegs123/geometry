import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2013_P4 : Prop :=
∀ (A B C W X Y : Point),
acute ⟨A, B, C⟩ →
let H := orthocenter ⟨A, B, C⟩;
on W (Seg.mk B C) →
let M := foot B (Line.mk A C);
let N := foot C (Line.mk A B);
let ω₁ := circumcircle ⟨B, W, N⟩;
on X ω₁ →
Circle.isDiameter W X ω₁ →
let ω₂ := circumcircle ⟨C, W, M⟩;
on Y ω₂ →
Circle.isDiameter W Y ω₂ →
coll X Y H

end Geo
