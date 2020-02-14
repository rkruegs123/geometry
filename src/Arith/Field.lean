/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Proving equalities in fields, building on:

1. https://github.com/coq/coq/blob/master/plugins/setoid_ring/Field_theory.v
-/
import Init.Data.Nat
import Init.Data.Int
import Init.Data.Array
import Init.Control.EState
import Geo.Util
import Geo.Background.Array
import Geo.Arith.CRing

namespace Arith

universe u

-- TODO: notation for inv
class HasInv (α : Type u) :=
(inv : α → α)

open HasInv

class Field (α : Type u) extends CRing α, HasDiv α, HasInv α :=
(oneNotEqZero : (1 : α) ≠ (0 : α))
(divDef       : ∀ (x y : α), x / y = x * inv y)
(invCancel    : ∀ (x : α), x ≠ 0 → x * inv x = 1)

inductive FExpr : Type
| atom : Nat → FExpr
| nat  : Nat → FExpr
| add  : FExpr → FExpr → FExpr
| mul  : FExpr → FExpr → FExpr
| sub  : FExpr → FExpr → FExpr
| div  : FExpr → FExpr → FExpr
| neg  : FExpr → FExpr
| inv  : FExpr → FExpr
| pow  : FExpr → Nat → FExpr

namespace FExpr

def hasToString : FExpr → String
| atom x => "#" ++ toString x
| nat n  => toString n
| add e₁ e₂ => "(add " ++ hasToString e₁ ++ " " ++ hasToString e₂ ++ ")"
| mul e₁ e₂ => "(mul " ++ hasToString e₁ ++ " " ++ hasToString e₂ ++ ")"
| div e₁ e₂ => "(div " ++ hasToString e₁ ++ " " ++ hasToString e₂ ++ ")"
| sub e₁ e₂ => "(sub " ++ hasToString e₁ ++ " " ++ hasToString e₂ ++ ")"
| inv e     => "(inv " ++ hasToString e ++ ")"
| neg e     => "(neg " ++ hasToString e ++ ")"
| pow e k   => "(pow " ++ hasToString e ++ " " ++ toString k ++ ")"

instance : HasToString FExpr := ⟨hasToString⟩
instance : HasRepr FExpr := ⟨hasToString⟩
instance : HasOfNat FExpr   := ⟨nat⟩
instance : HasAdd FExpr     := ⟨add⟩
instance : HasMul FExpr     := ⟨mul⟩
instance : HasSub FExpr     := ⟨sub⟩
instance : HasPow FExpr Nat := ⟨pow⟩
instance : HasNeg FExpr     := ⟨neg⟩
instance : HasDiv FExpr     := ⟨div⟩
instance : HasInv FExpr     := ⟨inv⟩

def denote {α : Type u} [Field α] (xs : Array α) : FExpr → α
| atom x  => xs.get! x
| nat n   => ofNat α n
| add x y => denote x + denote y
| mul x y => denote x * denote y
| div x y => denote x / denote y
| sub x y => denote x - denote y
| pow x k => (denote x)^k
| inv x   => HasInv.inv (denote x)
| neg x   => - (denote x)

end FExpr

structure FieldNF : Type :=
(numer      : CRExpr)
(denom      : CRExpr := 1)
(conditions : Array CRExpr := #[])

namespace FieldNF

variables {α : Type u} [Field α]

def denote (xs : Array α) (nf : FieldNF) : α :=
(nf.numer.denote xs) / (nf.denom.denote xs)

def denoteConditions (xs : Array α) (nf : FieldNF) : Prop :=
nf.conditions.allP (λ c => c.denote xs ≠ 0)

instance : Inhabited FieldNF := ⟨{ numer := 1 }⟩
end FieldNF

namespace Normalize

open FExpr

-- TODO: no idea what this does yet
private def defaultIsIn : CRExpr → Nat → CRExpr → Nat → Option (Nat × CRExpr)
| p₁, k₁, p₂, k₂ =>
  if p₁ == p₂ then
    if k₁ < k₂ then some (0, p₂ ^ (k₂ - k₁))
    else if k₂ < k₁ then some (k₁ - k₂, 1)
    else some (0, 1)
  else
    none

theorem defaultIsInOk (p₁ p₂ p₃ : CRExpr) (k₁ k₂ k₃ : Nat) :
  defaultIsIn p₁ k₁ p₂ k₂ = some (k₃, p₃) → CRExpr.denotationsEq (p₂^k₂) (p₁^(k₁ - k₃) * p₃) ∧ k₃ < k₁ :=
WIP

private def isIn : CRExpr → Nat → CRExpr → Nat → Option (Nat × CRExpr)
| p₁, k₁, CRExpr.mul p₃ p₄, k₂ =>
  match isIn p₁ k₁ p₃ k₂ with
  | some (0, p₅) => some (0, p₅ * (p₄ ^ k₂))
  | some (k₃, p₅) =>
    match isIn p₁ k₃ p₄ k₂ with
    | some (k₄, p₆) => some (k₄, p₅ * p₆)
    | none => some (k₃, p₅ * p₄^k₂)
  | none =>
    match isIn p₁ k₁ p₄ k₂ with
    | some (k₃, p₅) => some (k₃, p₅ * (p₃ ^ k₂))
    | none => none
| p₁, k₁, CRExpr.pow p₃ 0, k₂ => none
| p₁, k₁, CRExpr.pow p₃ k₃, k₂ => isIn p₁ k₁ p₃ (k₂ * k₃)
| p₁, k₁, p₂, k₂ => defaultIsIn p₁ k₁ p₂ k₂


theorem isInOk (p₁ p₂ p₃ : CRExpr) (k₁ k₂ k₃: Nat) :
  isIn p₁ k₁ p₂ k₂ = some (k₃, p₃) → CRExpr.denotationsEq (p₂^k₂) (p₁^(k₁ - k₃) * p₃) :=
WIP

structure Split : Type :=
(left common right : CRExpr)

-- TODO: temporary, to support the panic
instance SplitInhabited : Inhabited Split := ⟨⟨0, 0, 0⟩⟩

private def splitAux : CRExpr → Nat → CRExpr → Split
| CRExpr.mul p₃ p₄, k, p₂ =>
  let s₁ := splitAux p₃ k p₂;
  let s₂ := splitAux p₄ k s₁.right;
  { left   := s₁.left * s₂.left,
    common := s₁.common * s₂.common,
    right  := s₂.right }
| CRExpr.pow p₃ 0,  _, p₂ => ⟨1, 1, p₂⟩
| CRExpr.pow p₃ k₃, k, p₂ => splitAux p₃ (k₃ * k) p₂
| p₁, k, p₂ =>
  match isIn p₁ k p₂ 1 with
  | some (0, p₃)  => ⟨1, p₁^k, p₃⟩
  | some (k₁, p₃) => ⟨p₁^k₁, p₁^(k-k₁), p₃⟩
  | none          => ⟨p₁^k, 1, p₂⟩

private def split (p₁ p₂ : CRExpr) : Split := splitAux p₁ 1 p₂

theorem splitOk (p₁ p₂ : CRExpr) :
  let s := split p₁ p₂;
  CRExpr.denotationsEq p₁ (s.left * s.common)
  ∧ CRExpr.denotationsEq p₂ (s.right * s.common)
  ∧ p₁ ≠ 0 → s.left ≠ 0
  ∧ p₂ ≠ 0 → s.right ≠ 0 :=
WIP

partial def norm : FExpr → FieldNF
| atom x  => { numer := CRExpr.atom x }
| nat n   => { numer := CRExpr.nat n }
| add x y =>
  let (x, y) := (norm x, norm y);
  let s := split x.denom y.denom;
  { numer := x.numer * s.right + y.numer * s.left,
    denom := s.left * s.right * s.common,
    conditions := x.conditions.append y.conditions }
| sub x y => norm $ x + (- y)
| mul x y =>
  let (x, y) := (norm x, norm y);
  let s₁ := split x.numer y.denom;
  let s₂ := split y.numer x.denom;
  { numer := s₁.left * s₂.left,
    denom := s₂.right * s₁.right,
    conditions := x.conditions.append y.conditions }
| neg x => let x := norm x; { numer := - x.numer, .. x }
| inv x =>
  let x := norm x;
  { numer := x.denom, denom := x.numer, conditions := x.conditions.push x.numer }
| div x y => norm (x * FExpr.inv y)
| pow x k => let x := norm x; { numer := x.numer^k, denom := x.denom^k, .. x }


theorem normOk {α : Type u} [Field α] (xs : Array α) (e : FExpr) :
  (norm e).denoteConditions xs → (norm e).denote xs = e.denote xs :=
WIP

end Normalize

def FExpr.norm : FExpr → FieldNF := @Normalize.norm

theorem FieldCorrect {α : Type u} [Field α] (xs : Array α) (e₁ e₂ : FExpr) :
  e₁.norm.denoteConditions xs →
  e₂.norm.denoteConditions xs →
  e₁.norm = e₂.norm → e₁.denote xs = e₂.denote xs :=
WIP

end Arith
