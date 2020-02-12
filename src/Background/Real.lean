import Geo.Util

axiom Real : Type
notation `ℝ` := Real

class HasPi (α : Type) : Type := (pi {} : α)
notation `π` := HasPi.pi

namespace Real

noncomputable instance : HasOfNat ℝ := ⟨SKIP⟩
noncomputable instance : HasAdd ℝ := ⟨SKIP⟩
noncomputable instance : HasMul ℝ := ⟨SKIP⟩
noncomputable instance : HasNeg ℝ := ⟨SKIP⟩
noncomputable instance : HasSub ℝ := ⟨SKIP⟩
noncomputable instance : HasDiv ℝ := ⟨SKIP⟩
noncomputable instance : HasMod ℝ := ⟨SKIP⟩
noncomputable instance : HasPi ℝ := ⟨SKIP⟩
noncomputable instance : HasPow ℝ Nat := ⟨SKIP⟩
noncomputable instance : HasLess ℝ := ⟨SKIP⟩
noncomputable instance : HasLessEq ℝ := ⟨SKIP⟩

noncomputable def sqrt : ℝ → ℝ := SKIP
end Real

def PReal : Type := { x : ℝ // x > 0 }
notation `ℝ₊` := PReal

namespace PReal

noncomputable instance : HasOfNat ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasAdd ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasMul ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasNeg ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasSub ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasDiv ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasMod ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasPi ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasPow ℝ₊ Nat := ⟨SKIP⟩
noncomputable instance : HasLess ℝ₊ := ⟨SKIP⟩
noncomputable instance : HasLessEq ℝ₊ := ⟨SKIP⟩

end PReal

def NNReal : Type := { x : ℝ // x ≥ 0 }
notation `ℝ≥` := NNReal

namespace NNReal

noncomputable instance : HasOfNat ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasAdd ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasMul ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasNeg ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasSub ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasDiv ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasMod ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasPi ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasPow ℝ≥ Nat := ⟨SKIP⟩
noncomputable instance : HasLess ℝ≥ := ⟨SKIP⟩
noncomputable instance : HasLessEq ℝ≥ := ⟨SKIP⟩

end NNReal

def RealMod2π : Type := Quot (λ (x y : ℝ) => x % (2 * π) = y % 2 * π)
notation `ℝ2π` := RealMod2π

namespace RealMod2π

noncomputable instance : HasOfNat ℝ2π := ⟨SKIP⟩
noncomputable instance : HasAdd ℝ2π := ⟨SKIP⟩
noncomputable instance : HasNeg ℝ2π := ⟨SKIP⟩
noncomputable instance : HasSub ℝ2π := ⟨SKIP⟩
noncomputable instance : HasPi ℝ2π := ⟨SKIP⟩

end RealMod2π

def RealModπ : Type := Quot (λ (x y : ℝ) => x % π = y % π)
notation `ℝπ` := RealModπ

namespace RealModπ

noncomputable instance : HasOfNat ℝπ := ⟨SKIP⟩
noncomputable instance : HasAdd ℝπ := ⟨SKIP⟩
noncomputable instance : HasNeg ℝπ := ⟨SKIP⟩
noncomputable instance : HasSub ℝπ := ⟨SKIP⟩

end RealModπ
