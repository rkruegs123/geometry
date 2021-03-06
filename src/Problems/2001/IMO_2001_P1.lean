import Geo.Geo.Core

namespace Geo

open Analytic Triangle

def IMO_2001_P1 : Prop :=
∀ (A B C : Point),
acute ⟨A, B, C⟩ →
let O := circumcenter ⟨A, B, C⟩;
let P := foot A ⟨B, C⟩;
-- TODO: notation
(π : ℝ2π).divNat 6 + uangle ⟨A, B, C⟩ ≤ uangle ⟨B, C, A⟩ → -- BCA >= ABC + 30
(π : ℝ2π).divNat 2 > uangle ⟨C, A, B⟩ + uangle ⟨C, O, P⟩ -- CAB + COP < 90

end Geo
