import Geo.Geo.Core

namespace Geo

open Triangle

def IMO_2000_P6 : Prop :=
∀ (A₁ A₂ A₃ : Point),
acute ⟨A₁, A₂, A₃⟩ →
let Ks := Triple.map (λ (alt : Seg) => alt.dst) (altitudes ⟨A₁, A₂, A₃⟩);
-- Gergonne triangle is triangle with incenter contact points
let Ls := (gergonneTriangle ⟨A₁, A₂, A₃⟩).vertices;
let reflectedLines := Triple.map₂ (λ (kPair lPair : Point × Point) =>
reflect (Line.mk kPair.fst kPair.snd) (Line.mk lPair.fst lPair.snd))
Ks.cyclicPairs Ls.cyclicPairs;
(Triangle.buildLLL reflectedLines).vertices.all (λ (p : Point) => on p (incircle ⟨A₁, A₂, A₃⟩))

end Geo
