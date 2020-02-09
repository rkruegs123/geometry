axiom SKIP {α : Type} : α
axiom SORRY {α : Prop} : α

def unique {α : Type} (p : α → Prop) (x : α) : Prop :=
p x ∧ ∀ y, p y → y = x
