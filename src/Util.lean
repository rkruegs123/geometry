axiom SKIP {α : Type} : α
axiom SORRY {α : Prop} : α

def unique {α : Type} (p : α → Prop) (x : α) : Prop :=
p x ∧ ∀ y, p y → y = x

universe u
instance HasZeroOfHasNat {α : Type u} [HasOfNat α] : HasZero α := ⟨ofNat α 0⟩
instance HasOneOfHasNat  {α : Type u} [HasOfNat α] : HasOne  α := ⟨ofNat α 1⟩
instance InhabitedOfHasZero {α : Type u} [HasZero α] : Inhabited α := ⟨0⟩
