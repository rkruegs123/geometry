axiom SKIP {α : Type} : α
axiom SORRY {α : Prop} : α

def unique {α : Type} (p : α → Prop) (x : α) : Prop :=
p x ∧ ∀ y, p y → y = x

namespace List

def allP {α : Type} (l : List α) (p : α → Prop) : Prop :=
foldr (fun a r => p a ∧ r) true l

end List
