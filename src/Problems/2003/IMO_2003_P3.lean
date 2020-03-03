import Geo.Geo.Core

namespace Geo

open Analytic Polygon

def IMO_2003_P3 : Prop :=
∀ (hex : Polygon 6),
convex hex →
(hex.oppoSides rfl).allP (λ oPair =>
  let midpDist := dist oPair.fst.midp oPair.snd.midp;
  let sumLengths := ulen oPair.fst + ulen oPair.snd;
  midpDist = (Real.sqrt 3) / 2 * sumLengths
) →
hex.angles.allEq

end Geo
