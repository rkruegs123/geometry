structure Triple (α : Type) : Type := (A B C : α)

namespace Triple

variables {α β γ : Type}

def map (f : α → β) : Triple α → Triple β
| ⟨A, B, C⟩ => ⟨f A, f B, f C⟩

def map₂ (f : α → β → γ) : Triple α → Triple β → Triple γ
| ⟨A₁, B₁, C₁⟩, ⟨A₂, B₂, C₂⟩ => ⟨f A₁ A₂, f B₁ B₂, f C₁ C₂⟩

instance : Functor Triple := { map := @map }

def cycle : Triple α → Triple α
| ⟨A, B, C⟩ => ⟨B, C, A⟩

def cycles (t : Triple α) : Triple (Triple α) :=
⟨t, t.cycle, t.cycle.cycle⟩

-- ryankrue: maybe there is a way to do this with cmap
def uniquePairs (t : Triple α) : Triple (α × α) :=
Triple.map (λ (cyc : Triple α) => Prod.mk cyc.A cyc.B) t.cycles

def cmap (f : Triple α → β) (t : Triple α) : Triple β :=
f <$> t.cycles

-- TODO: much more abstract typeclass?
def any (p : α → Prop) : Triple α → Prop
| ⟨A, B, C⟩ => p A ∨ p B ∨ p C

def all (p : α → Prop) : Triple α → Prop
| ⟨A, B, C⟩ => p A ∧ p B ∧ p C

end Triple

structure Quadruple (α : Type) : Type := (A B C D : α)

namespace Quadruple

variables {α β : Type}

def map (f : α → β) : Quadruple α → Quadruple β
| ⟨A, B, C, D⟩ => ⟨f A, f B, f C, f D⟩

instance : Functor Quadruple := { map := @map }

def cycle : Quadruple α → Quadruple α
| ⟨A, B, C, D⟩ => ⟨B, C, D, A⟩

def cycles (t : Quadruple α) : Quadruple (Quadruple α) :=
⟨t, t.cycle, t.cycle.cycle, t.cycle.cycle.cycle⟩

def cmap (f : Quadruple α → β) (t : Quadruple α) : Quadruple β :=
f <$> t.cycles

-- TODO: much more abstract typeclass?
def any (p : α → Prop) : Quadruple α → Prop
| ⟨A, B, C, D⟩ => p A ∨ p B ∨ p C ∨ p D

def all (p : α → Prop) : Quadruple α → Prop
| ⟨A, B, C, D⟩ => p A ∧ p B ∧ p C ∧ p D

end Quadruple
