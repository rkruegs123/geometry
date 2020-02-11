import Geo.Geo.Core

namespace Geo

open Analytic Polygon

def IMO_2003_P3 : Prop :=
∀ (hex : Polygon 6),
convex hex →
(hex.oppoSides rfl).allP (λ ⟨s₁, s₂⟩ =>
  let midpDist := dist s₁.midp s₂.midp;
  let sumLengths := ulen s₁ + ulen s₂;
  midpDist = (Real.sqrt 3) / 2 * sumLengths
) →
hex.angles.allEq

end Geo
