import Geo.Geo.Core

namespace Geo


open Geo.Triangle



def IMO_2017_P3 : Prop :=
∀ (A B C H O P Q : Point),
acute ⟨A, B, C⟩ →
scalene ⟨A, B, C⟩ →
circumcenter ⟨A, B, C⟩ = O → -- or should this be assume?
intersectAt (Line.mk O A) (Line.mk B (foot B ⟨A, C⟩)) P → -- could make cleaner with altitudes def
intersectAt (Line.mk O A) (Line.mk C (foot C ⟨A, B⟩)) Q → -- could make cleaner with altitudes def
orthocenter ⟨A, B, C⟩ = H → -- altitudes meet at H
let δ := circumcenter ⟨P, Q, H⟩; -- don't name, because it's not named in the problem
Triple.any (Line.on δ) $ medians ⟨A, B, C⟩ -- circumcenter of a triangle PQH lies on a median of a triangle ABC. Note that we could also phrase an an Exists



end Geo
