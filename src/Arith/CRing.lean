/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Mario Carneiro

Proving equalities in commutative rings, building on:

1. https://github.com/leanprover-community/mathlib/blob/master/src/tactic/ring2.lean
2. Grégoire, B. and Mahboubi, A., 2005, August. Proving equalities in a commutative ring done right in Coq.
-/
import Init.Data.Nat
import Init.Data.Int
import Init.Data.Array
import Init.Control.EState
import Geo.Util

namespace Arith

universe u

class CRing (α : Type u)
extends HasOfNat α, HasAdd α, HasMul α, HasSub α, HasNeg α, HasPow α Nat :=
(add0        : ∀ (x : α), x + 0 = x)
(addC        : ∀ (x y : α), x + y = y + x)
(addA        : ∀ (x y z : α), (x + y) + z = x + (y + z))
(mul0        : ∀ (x : α), x * 0 = 0)
(mul1        : ∀ (x : α), x * 1 = x)
(mulC        : ∀ (x y : α), x * y = y * x)
(mulA        : ∀ (x y z : α), (x * y) * z = x * (y * z))
(distribL    : ∀ (x y z : α), x * (y + z) = x * y + x * z)
(negMul      : ∀ (x y : α), - (x * y) = (- x) * y)
(negAdd      : ∀ (x y : α), - (x + y) = (- x) + (- y))
(subDef      : ∀ (x y : α), x - y = x + (- y))
(pow0        : ∀ (x : α), x^0 = 1)
(powS        : ∀ (x : α) (n : Nat), x^(n + 1) = x * x^n)

inductive CRExpr : Type
| atom : Nat → CRExpr
| nat  : Nat → CRExpr
| add  : CRExpr → CRExpr → CRExpr
| mul  : CRExpr → CRExpr → CRExpr
| sub  : CRExpr → CRExpr → CRExpr
| neg  : CRExpr → CRExpr
| pow  : CRExpr → Nat → CRExpr

namespace CRExpr

def hasBeq : CRExpr → CRExpr → Bool
| atom x₁,   atom x₂   => x₁ == x₂
| nat n₁,    nat n₂    => n₁ == n₂
| add x₁ y₁, add x₂ y₂ => hasBeq x₁ x₂ && hasBeq y₁ y₂
| mul x₁ y₁, mul x₂ y₂ => hasBeq x₁ x₂ && hasBeq y₁ y₂
| sub x₁ y₁, sub x₂ y₂ => hasBeq x₁ x₂ && hasBeq y₁ y₂
| neg x₁,    neg x₂    => hasBeq x₁ x₂
| pow x₁ k₁, pow x₂ k₂ => hasBeq x₁ x₂ && k₁ == k₂
| _,         _         => false

instance : HasBeq CRExpr := ⟨hasBeq⟩

def hasToString : CRExpr → String
| atom x => "#" ++ toString x
| nat n  => toString n
| add e₁ e₂ => "(add " ++ hasToString e₁ ++ " " ++ hasToString e₂ ++ ")"
| mul e₁ e₂ => "(mul " ++ hasToString e₁ ++ " " ++ hasToString e₂ ++ ")"
| sub e₁ e₂ => "(sub " ++ hasToString e₁ ++ " " ++ hasToString e₂ ++ ")"
| neg e     => "(neg " ++ hasToString e ++ ")"
| pow e k   => "(pow " ++ hasToString e ++ " " ++ toString k ++ ")"

instance : HasToString CRExpr := ⟨hasToString⟩
instance : HasRepr CRExpr := ⟨hasToString⟩
instance : HasOfNat CRExpr   := ⟨nat⟩
instance : HasAdd CRExpr     := ⟨add⟩
instance : HasMul CRExpr     := ⟨mul⟩
instance : HasSub CRExpr     := ⟨sub⟩
instance : HasPow CRExpr Nat := ⟨pow⟩
instance : HasNeg CRExpr     := ⟨neg⟩

def denote {α : Type u} [CRing α] (xs : Array α) : CRExpr → α
| atom x  => xs.get! x
| nat n   => ofNat α n
| add x y => denote x + denote y
| mul x y => denote x * denote y
| sub x y => denote x - denote y
| pow x k => (denote x)^k
| neg x   => - (denote x)

end CRExpr

abbrev Atom := Nat
abbrev Power := Nat

-- Horner expressions
-- Note: care must be taken to maintain "canonical forms"
inductive HExpr : Type
| int       : Int → HExpr
| hornerAux : ∀ (a : HExpr) (x : Atom) (k : Power) (b : HExpr), HExpr -- a[x]^k + b

namespace HExpr

def hasToString : HExpr → String
| int k => "!" ++ toString k
| hornerAux a x k b => "(h " ++ hasToString a ++ " " ++ toString x ++ " " ++ toString k ++ " " ++ hasToString b ++ ")"

instance : HasToString HExpr := ⟨hasToString⟩
instance : HasRepr HExpr := ⟨hasToString⟩

instance : HasOfNat HExpr  := ⟨λ n => int n⟩

def hasBeq : HExpr → HExpr → Bool
| int n₁, int n₂ => n₁ == n₂
| hornerAux a₁ x₁ k₁ b₁, hornerAux a₂ x₂ k₂ b₂ => hasBeq a₁ a₂ && x₁ == x₂ && k₁ == k₂ && hasBeq b₁ b₂
| _, _ => false

instance : HasBeq HExpr := ⟨hasBeq⟩

def atom (x : Atom) : HExpr := hornerAux 1 x 1 0

-- Constructor that maintains canonical form.
def horner (a : HExpr) (x : Atom) (k : Power) (b : HExpr) : HExpr :=
match a with
| int c                 =>
  if c = 0 then b else hornerAux a x k b
| hornerAux a₁ x₁ k₁ b₁ =>
  if x₁ = x ∧ b₁ == 0 then hornerAux a₁ x (k₁ + k) b else hornerAux a x k b

/-
-- The "correct" version, but the compiler can't find "recOn"
def addConst (c₁ : Int) (e₂ : HExpr) : HExpr :=
if c₁ == 0 then e₂ else
  @HExpr.recOn (λ _ => HExpr) e₂
             (λ (c₂ : Int) => int (c₁ + c₂))
             (λ a₂ x₂ k₂ b₂ _ B₂ => hornerAux a₂ x₂ k₂ B₂)
-/
def addConstCore (c₁ : Int) : Nat → HExpr → HExpr
| 0, e₂ => panic! "addConstCore out of fuel"
| fuel+1, e₂ =>
  if c₁ == 0 then e₂ else
    match e₂ with
    | int c₂ => int (c₁ + c₂)
    | hornerAux a₂ x₂ k₂ b₂ => hornerAux a₂ x₂ k₂ (addConstCore fuel b₂)

def addConst (c₁ : Int) (e₂ : HExpr) : HExpr :=
addConstCore c₁ 10000 e₂

def addAux (a₁ : HExpr) (addA₁ : HExpr → HExpr) (x₁ : Atom) : HExpr → Power → HExpr → (HExpr → HExpr) → HExpr
| int c₂,                     k₁, b₁, ϕ =>
  addConst c₂ (hornerAux a₁ x₁ k₁ b₁)
| e₂@(hornerAux a₂ x₂ k₂ b₂), k₁, b₁, ϕ =>
  if x₁ < x₂ then hornerAux a₁ x₁ k₁ (ϕ e₂)
  else if x₂ < x₁ then hornerAux a₂ x₂ k₂ (addAux b₂ k₁ b₁ ϕ)
  else if k₁ < k₂ then hornerAux (addA₁ $ hornerAux a₂ x₁ (k₂ - k₁) 0) x₁ k₁ (ϕ b₂)
  else if k₂ < k₁ then hornerAux (addAux a₂ (k₁ - k₂) 0 id) x₁ k₂ (ϕ b₂)
  else horner (addA₁ a₂) x₁ k₁ (ϕ b₂)

def add : HExpr → HExpr → HExpr
| int c₁,                e₂ => addConst c₁ e₂
| hornerAux a₁ x₁ k₁ b₁, e₂ => addAux a₁ (add a₁) x₁ e₂ k₁ b₁ (add b₁)

instance : HasAdd HExpr := ⟨add⟩

def neg : HExpr → HExpr
| int n => int (-n)
| hornerAux a x k b => hornerAux (neg a) x k (neg b)

instance : HasNeg HExpr := ⟨neg⟩

/-
The "correct" version. See `addConst` above for context.
def mulConst (c₁ : Int) (e₂ : HExpr) : HExpr :=
if c₁ == 0 then 0
else if c₁ == 1 then e₂
else @HExpr.recOn (λ _ => HExpr) e₂
             (λ (c₂ : Int) => int (c₁ * c₂))
             (λ a₂ x₂ k₂ b₂ A₂ B₂ => hornerAux A₂ x₂ k₂ B₂)
-/

def mulConstCore (c₁ : Int) : Nat → HExpr → HExpr
| 0, e₂ => panic! "mulConstCore out of fuel"
| fuel+1, e₂ =>
  if c₁ == 0 then 0
  else if c₁ == 1 then e₂
  else match e₂ with
       | int c₂ => int (c₁ * c₂)
       | hornerAux a₂ x₂ k₂ b₂ => hornerAux (mulConstCore fuel a₂) x₂ k₂ (mulConstCore fuel b₂)

def mulConst (c₁ : Int) (e₂ : HExpr) : HExpr :=
mulConstCore c₁ 10000 e₂

def mulAux (a₁ : HExpr) (x₁ : Atom) (k₁ : Power) (b₁ : HExpr) (mulA₁ mulB₁ : HExpr → HExpr) : HExpr → HExpr
| int k₂ => mulConst k₂ (horner a₁ x₁ k₁ b₁)
| e₂@(hornerAux a₂ x₂ k₂ b₂) =>
  if x₁ < x₂ then horner (mulA₁ e₂) x₁ k₁ (mulB₁ e₂)
  else if x₂ < x₁ then horner (mulAux a₂) x₂ k₂ (mulAux b₂)
  else
    let t : HExpr := horner (mulAux a₂) x₁ k₂ 0;
    if b₂ == 0 then t else t + horner (mulA₁ b₂) x₁ k₁ (mulB₁ b₂)

def mul : HExpr → HExpr → HExpr
| int k₁                => mulConst k₁
| hornerAux a₁ x₁ k₁ b₁ => mulAux a₁ x₁ k₁ b₁ (mul a₁) (mul b₁)

instance : HasMul HExpr := ⟨mul⟩

def pow (t : HExpr) : Nat → HExpr
| 0 => 1
| 1 => t
| k+1 => t * pow k

instance : HasPow HExpr Nat := ⟨pow⟩

end HExpr

namespace CRExpr

def toHExpr : CRExpr → HExpr
| atom x => HExpr.atom x
| nat n  => HExpr.int n
| add x y => x.toHExpr + y.toHExpr
| sub x y => x.toHExpr + - y.toHExpr
| mul x y => x.toHExpr * y.toHExpr
| neg x   => - x.toHExpr
| pow x k => x.toHExpr ^ k

end CRExpr

namespace HExpr

def denote {α : Type u} [CRing α] (xs : Array α) : HExpr → α
| HExpr.int n                 => if n ≥ 0 then ofNat α n.natAbs else - (ofNat α $ n.natAbs)
| HExpr.hornerAux a x k b => a.denote * (xs.get! x)^k + b.denote

-- TODO: this theorem is not true until we either restore primitive recursion
-- or switch to returning an Option.
axiom denoteCommutes {α : Type u} [CRing α] (xs : Array α) :
  ∀ (r : CRExpr), r.denote xs = r.toHExpr.denote xs

end HExpr

axiom HCorrect (α : Type u) [CRing α] (xs : Array α) (r₁ r₂ : CRExpr) :
  r₁.toHExpr = r₂.toHExpr → r₁.denote xs = r₂.denote xs

end Arith
