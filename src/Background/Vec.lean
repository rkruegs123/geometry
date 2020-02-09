import Geo.Util
import Geo.Background.Nat
import Geo.Background.List


def Vec (X : Type) (n : Nat) : Type :=
{ xs : List X // xs.length == n }

namespace Vec

variables {X Y Z : Type} {n n₁ n₂ : Nat}

axiom get : Vec X n → Fin n → X

-- TODO(dselsam): unsound
noncomputable def get₀ (v : Vec X n) : X := v.get ⟨0, SORRY⟩
noncomputable def get₁ (v : Vec X n) : X := v.get ⟨1, SORRY⟩
noncomputable def get₂ (v : Vec X n) : X := v.get ⟨2, SORRY⟩
noncomputable def get₃ (v : Vec X n) : X := v.get ⟨3, SORRY⟩

axiom fromFunc (f : Fin n → X) : Vec X n

axiom rcons (v : Vec X n) (x : X) : Vec X (n+1)

axiom getRest (v : Vec X n) (i : Fin n) : Vec X n.pred

axiom fromFin {X : Type} {n : Nat} (f : Fin n → X) : Vec X n

def empty : Vec X 0 :=
⟨ [], rfl ⟩

def take (k : Fin n) (xs : Vec X n) : Vec X k.val :=
⟨ xs.val.take k.val, SORRY ⟩

def drop (k : Fin n) (xs : Vec X n) : Vec X (n - k.val) :=
⟨ xs.val.drop k.val, SORRY ⟩

def append (xs₁ : Vec X n₁) (xs₂ : Vec X n₂) : Vec X (n₁ + n₂) :=
⟨ xs₁.val ++ xs₂.val, SORRY ⟩

def range (n : Nat) : Vec (Fin n) n :=
⟨ List.rangeFin n, SORRY ⟩

def map (f : X -> Y) (xs : Vec X n) : Vec Y n :=
⟨ List.map f xs.val, SORRY ⟩

def map₂ (f : X → Y → Z) (xs : Vec X n) (ys : Vec Y n) : Vec Z n :=
⟨ List.map₂ f xs.val ys.val, SORRY ⟩

def sum [HasZero X] [HasAdd X] (xs : Vec X n) : X :=
List.sum xs.val

def prod [HasOne X] [HasMul X] (xs : Vec X n) : X :=
List.prod xs.val

def cycle (k : Fin n) (xs : Vec X n) : Vec X n :=
cast SORRY ((xs.drop k).append (xs.take k))

def cycle₁ (xs : Vec X n) : Vec X n :=
cast SORRY ((xs.drop ⟨1, SORRY⟩).append (xs.take ⟨1, SORRY⟩))

def cycle₂ (xs : Vec X n) : Vec X n :=
cast SORRY ((xs.drop ⟨2, SORRY⟩).append (xs.take ⟨2, SORRY⟩))

def cycles (xs : Vec X n) : Vec (Vec X n) n :=
(range n).map (λ (k : Fin n) => cycle k xs)

def cyclicSum [HasZero Y] [HasAdd Y] (xs : Vec X n) (f : Vec X n → Y) : Y :=
(xs.cycles.map f).sum

def subvecs (k : Fin n) (xs : Vec X n) : Vec (Vec X k.val) (n.choose k) :=
cast SORRY (xs.val.sublists k.val)

axiom mapReducePairs (f : X → X → Y) (xs : Vec X n) : Vec Y n

def replicate (n : Nat) (x : X) : Vec X n :=
⟨ List.replicate n x, SORRY ⟩

axiom mem : Vec X n → X → Prop
axiom hasSubvec {k : Nat} : Vec X n → Vec X k → Prop
axiom allDistinct {n : Nat} : Vec X n → Prop
axiom allEq {n : Nat} : Vec X n → Prop
axiom allP {n : Nat} : Vec X n → (X → Prop) → Prop

def lt (lt : X → X → Bool) (xs ys : Vec X n) : Bool :=
List.lt lt xs.val ys.val

end Vec
