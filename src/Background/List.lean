import Geo.Util

namespace List

universes u v
variables {α : Type u} {β : Type v}

@[inline] def all₂Core (p : α → β → Bool) : List α → List β → Bool
| [], [] => true
| x::xs, y::ys => p x y && all₂Core xs ys
| _, _ => false

@[inline] def all₂ (p : α → β → Bool) (l₁ : List α) (l₂ : List β) : Bool :=
l₁.length == l₂.length && all₂Core p l₁ l₂

def allP (l : List α) (p : α → Prop) : Prop :=
foldr (fun a r => p a ∧ r) true l

def allEq : List α → Prop
| [] => true
| [x] => true
| x::y::xs => x = y ∧ allEq (y::xs)

def allDistinct (l : List α) : Prop :=
WIP

noncomputable def distinctPairs (l : List α) : List (α × α) :=
WIP

def rangeFinAux (n : Nat) : ∀ (k : Nat), k ≤ n → List (Fin n) → List (Fin n)
| 0,   H, ns => ns
| k+1, H, ns => let H₁ : k < n := H;
                let H₂ : k ≤ n := WIP;
                rangeFinAux k H₂ (⟨k, H₁⟩ :: ns)

def rangeFin (n : Nat) : List (Fin n) :=
rangeFinAux n n (Nat.leRefl n) []

def sublists : Nat -> List α -> List (List α)
| 0,   xs      => [[]]
| k+1, []      => []
| k+1, (x::xs) => (sublists k xs).map (λ ys => x :: ys) ++ sublists (k+1) xs

def sum [HasZero α] [HasAdd α] (xs : List α) : α := xs.foldl HasAdd.add 0
def prod [HasOne α] [HasMul α] (xs : List α) : α := xs.foldl HasMul.mul 1
def max (lt : α -> α -> Bool) (x₀ : α) (xs : List α) := xs.foldl (λ xₘ x => if lt xₘ x then x else xₘ) x₀

def ltCore (ltα : α -> α -> Bool) : List α → List α → Bool
| x1::xs1, x2::xs2 => if ltα x1 x2 then true else if ltα x2 x1 then false else ltCore xs1 xs2
| _, _ => false

def lt (ltα : α -> α -> Bool) (xs₁ xs₂ : List α) : Bool :=
if xs₁.length < xs₂.length then true else
if xs₂.length < xs₁.length then false else
ltCore ltα xs₁ xs₂

def cycle (k : Nat) (xs : List α) : List α :=
(xs.drop k).append (xs.take k)

def cycles (xs : List α) : List (List α) :=
(List.range xs.length).map (λ (k : Nat) => cycle k xs)

partial def cartesianProduct : List (List α) → List (List α)
| []        => [[]]
| (xs::xss) =>
  let cpxss : List (List α) := cartesianProduct xss;
  (xs.map (λ x => cpxss.map (λ xs => x::xs))).join

end List
