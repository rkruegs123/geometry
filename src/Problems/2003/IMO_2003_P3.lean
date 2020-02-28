import Geo.Geo.Core

namespace Geo

open Analytic Polygon

def IMO_2003_P3 : Prop :=
∀ (hex : Polygon 6),
convex hex →
let midp_dist₀₃ := dist ((hex.sides.get 0).midp) ((hex.sides.get 3).midp);
let midp_dist₁₄ := dist ((hex.sides.get 1).midp) ((hex.sides.get 4).midp);
let midp_dist₂₅ := dist ((hex.sides.get 2).midp) ((hex.sides.get 5).midp);
let sum_lengths₀₃ := ulen (hex.sides.get 0) + ulen (hex.sides.get 3);
let sum_lengths₁₄ := ulen (hex.sides.get 1) + ulen (hex.sides.get 4);
let sum_lengths₂₅ := ulen (hex.sides.get 2) + ulen (hex.sides.get 5);
midp_dist₀₃ = (Real.sqrt 3) / 2 * sum_lengths₀₃ →
midp_dist₁₄ = (Real.sqrt 3) / 2 * sum_lengths₁₄ →
midp_dist₂₅ = (Real.sqrt 3) / 2 * sum_lengths₂₅ →
hex.angles.allEq

end Geo
