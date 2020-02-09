import Geo.Util

namespace List

@[inline] def all₂Core {α β : Type*} (p : α → β → Bool) : List α → List β → Bool
| [], [] => true
| x::xs, y::ys => p x y && all₂Core xs ys
| _, _ => false

@[inline] def all₂ {α β : Type*} (p : α → β → Bool) (l₁ : List α) (l₂ : List β) : Bool :=
l₁.length == l₂.length && all₂Core p l₁ l₂

def allP {α : Type} (l : List α) (p : α → Prop) : Prop :=
foldr (fun a r => p a ∧ r) true l

def allEq {α : Type} : List α → Prop
| [] => true
| [x] => true
| x::y::xs => x = y ∧ allEq (y::xs)

def allDistinct {α : Type} (l : List α) : Prop :=
SKIP

noncomputable def distinctPairs {α : Type} (l : List α) : List (α × α) :=
SKIP

def rangeFinAux (n : Nat) : ∀ (k : Nat), k ≤ n → List (Fin n) → List (Fin n)
| 0,   H, ns => ns
| k+1, H, ns => let H₁ : k < n := H;
                let H₂ : k ≤ n := SORRY;
                rangeFinAux k H₂ (⟨k, H₁⟩ :: ns)

def rangeFin (n : Nat) : List (Fin n) :=
rangeFinAux n n (Nat.leRefl n) []

def sublists {X : Type} : Nat -> List X -> List (List X)
| 0,   xs      => [[]]
| k+1, []      => []
| k+1, (x::xs) => (sublists k xs).map (λ ys => x :: ys) ++ sublists (k+1) xs

def sum {X : Type} [HasZero X] [HasAdd X] (xs : List X) : X := xs.foldl HasAdd.add 0
def prod {X : Type} [HasOne X] [HasMul X] (xs : List X) : X := xs.foldl HasMul.mul 1
def max {X : Type} (lt : X -> X -> Bool) (x₀ : X) (xs : List X) := xs.foldl (λ xₘ x => if lt xₘ x then x else xₘ) x₀

def ltCore {X : Type} (ltX : X -> X -> Bool) : List X → List X → Bool
| x1::xs1, x2::xs2 => if ltX x1 x2 then true else if ltX x2 x1 then false else ltCore xs1 xs2
| _, _ => false

def lt {X : Type} (ltX : X -> X -> Bool) (xs₁ xs₂ : List X) : Bool :=
if xs₁.length < xs₂.length then true else
if xs₂.length < xs₁.length then false else
ltCore ltX xs₁ xs₂

def cycle {X : Type} (k : Nat) (xs : List X) : List X :=
(xs.drop k).append (xs.take k)

def cycles {X : Type} (xs : List X) : List (List X) :=
(List.range xs.length).map (λ (k : Nat) => cycle k xs)

partial def cartesianProduct {A : Type} : List (List A) → List (List A)
| []        => [[]]
| (xs::xss) =>
  let cpxss : List (List A) := cartesianProduct xss;
  (xs.map (λ x => cpxss.map (λ xs => x::xs))).join

end List
