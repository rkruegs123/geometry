import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2000_P6 : Prop :=
∀ (A₁ A₂ A₃ L₁ L₂ L₃ : Point),
acute ⟨A₁, A₂, A₃⟩ →
let Ks := Triple.map (λ (alt : Seg) => alt.dst) (altitudes ⟨A₁, A₂, A₃⟩);
/-
ryankrue: Alternative ways of dealing with Ls (see Geo/Core.lean for additional notes):
-quantify over L₁ L₂ L₃
-let Ls := Triple.map (λ (side : Seg) => intersectionPoint side (incircle ⟨A₁, A₂, A₃⟩))
(Triangle.sides ⟨A₁, A₂, A₃⟩);
-/
let Ls := (gergonneTriangle ⟨A₁, A₂, A₃⟩).vertices;
let reflected_lines := Triple.map₂ (λ (kpair lpair : Point × Point) => 
reflect (Line.mk kpair.fst kpair.snd) (Line.mk lpair.fst lpair.snd)) 
Ks.uniquePairs Ls.uniquePairs;
(Triangle.buildLLL reflected_lines).vertices.all (λ (p : Point) => on p (incircle ⟨A₁, A₂, A₃⟩))

end Geo
