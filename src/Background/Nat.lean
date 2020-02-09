namespace Nat

def fact : Nat -> Nat
| 0 => 1
| 1 => 1
| n+1 => (n+1) * fact n

def choose (n : Nat) (k : Fin n) : Nat :=
n.fact / (k.val.fact * (n-k.val).fact)

partial def gcd : Nat → Nat → Nat
| a, b => if b == 0 then a else gcd b (a % b)

end Nat
