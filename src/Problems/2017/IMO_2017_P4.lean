import Geo.Geo.Core

namespace Geo

open Triangle
open Circle

/- 
Note: A₂ is a placeholder for the second point of intersection b/w Γ and l, 
and is not named in the problem
-/

def IMO_2017_P4 : Prop :=
∀ (A A₂ J K R S T : Point) (Ω : Circle),
on R Ω →
on S Ω →
¬isDiameter R S Ω → -- ryankrue: note we couldn't use isDiameter₂ here
let l := lineTangentAtP Ω R;
S = midp (Seg.mk R T) → -- ryankrue: note how we don't use let here
on J (Arc.buildMinor Ω R S) →
let Γ := circumcircle ⟨J, S, T⟩;
intersectAtt₂ Γ l A A₂ →
Geo.Analytic.dist A R < Geo.Analytic.dist A₂ R →
/- 
The above corresponds to the following in the problem statement:

"Let A be the common points of αnd l is closer to R"

-/
intersectAt (Line.mk A J) Ω K →
tangent (Line.mk K T) Γ

end Geo
