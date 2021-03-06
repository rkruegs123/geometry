import Geo.Geo.Core

namespace Geo

open Circle Seg Triangle

def IMO_2013_P4 : Prop :=
∀ (A B C W : Point),
acute ⟨A, B, C⟩ →
let H := orthocenter ⟨A, B, C⟩;
strictlyBtw W B C →
let M := foot B (Line.mk A C);
let N := foot C (Line.mk A B);
∀ (X Y : Point),
let ω₁ := Triangle.circumcircle ⟨B, W, N⟩;
on X ω₁ →
isDiameter W X ω₁ →
let ω₂ := Triangle.circumcircle ⟨C, W, M⟩;
on Y ω₂ →
isDiameter W Y ω₂ →
coll X Y H

end Geo
