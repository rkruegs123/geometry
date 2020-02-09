import Geo.Background.Real

def Set (X : Type) : Type := X → Prop
--def Set.mem {X : Type} (x : X) (s : Set X) : Prop := s x
--def Set.nonEmpty {X : Type} (s : Set X) : Prop := Exists (λ x => s.mem x)
axiom Set.finiteCard {X : Type} : Set X → Option Nat
axiom Set.min {X : Type} (s : Set X) (H : Exists s) (opt : X → ℝ≥) : X
