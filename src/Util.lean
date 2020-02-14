axiom WIP.{u} {α : Sort u} : α
--axiom WIP {α : Prop} : α

universe u
variable {α : Type u}

def unique (p : α → Prop) (x : α) : Prop := p x ∧ ∀ y, p y → y = x
instance HasZeroOfHasNat {α : Type u} [HasOfNat α] : HasZero α := ⟨ofNat α 0⟩
instance HasOneOfHasNat  {α : Type u} [HasOfNat α] : HasOne  α := ⟨ofNat α 1⟩
instance InhabitedOfHasZero {α : Type u} [HasZero α] : Inhabited α := ⟨0⟩
