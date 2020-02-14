import Geo.Util

axiom Real : Type
notation `ℝ` := Real

class HasPi (α : Type) : Type := (pi {} : α)
notation `π` := HasPi.pi

namespace Real

noncomputable instance : HasOfNat ℝ := ⟨WIP⟩
noncomputable instance : HasAdd ℝ := ⟨WIP⟩
noncomputable instance : HasMul ℝ := ⟨WIP⟩
noncomputable instance : HasNeg ℝ := ⟨WIP⟩
noncomputable instance : HasSub ℝ := ⟨WIP⟩
noncomputable instance : HasDiv ℝ := ⟨WIP⟩
noncomputable instance : HasMod ℝ := ⟨WIP⟩
noncomputable instance : HasPi ℝ := ⟨WIP⟩
noncomputable instance : HasPow ℝ Nat := ⟨WIP⟩
noncomputable instance : HasLess ℝ := ⟨WIP⟩
noncomputable instance : HasLessEq ℝ := ⟨WIP⟩

noncomputable def sqrt : ℝ → ℝ := WIP
end Real

def PReal : Type := { x : ℝ // x > 0 }
notation `ℝ₊` := PReal

namespace PReal

noncomputable instance : HasOfNat ℝ₊ := ⟨WIP⟩
noncomputable instance : HasAdd ℝ₊ := ⟨WIP⟩
noncomputable instance : HasMul ℝ₊ := ⟨WIP⟩
noncomputable instance : HasNeg ℝ₊ := ⟨WIP⟩
noncomputable instance : HasSub ℝ₊ := ⟨WIP⟩
noncomputable instance : HasDiv ℝ₊ := ⟨WIP⟩
noncomputable instance : HasMod ℝ₊ := ⟨WIP⟩
noncomputable instance : HasPi ℝ₊ := ⟨WIP⟩
noncomputable instance : HasPow ℝ₊ Nat := ⟨WIP⟩
noncomputable instance : HasLess ℝ₊ := ⟨WIP⟩
noncomputable instance : HasLessEq ℝ₊ := ⟨WIP⟩

end PReal

def NNReal : Type := { x : ℝ // x ≥ 0 }
notation `ℝ≥` := NNReal

namespace NNReal

noncomputable instance : HasOfNat ℝ≥ := ⟨WIP⟩
noncomputable instance : HasAdd ℝ≥ := ⟨WIP⟩
noncomputable instance : HasMul ℝ≥ := ⟨WIP⟩
noncomputable instance : HasNeg ℝ≥ := ⟨WIP⟩
noncomputable instance : HasSub ℝ≥ := ⟨WIP⟩
noncomputable instance : HasDiv ℝ≥ := ⟨WIP⟩
noncomputable instance : HasMod ℝ≥ := ⟨WIP⟩
noncomputable instance : HasPi ℝ≥ := ⟨WIP⟩
noncomputable instance : HasPow ℝ≥ Nat := ⟨WIP⟩
noncomputable instance : HasLess ℝ≥ := ⟨WIP⟩
noncomputable instance : HasLessEq ℝ≥ := ⟨WIP⟩

end NNReal

def RealMod2π : Type := Quot (λ (x y : ℝ) => x % (2 * π) = y % 2 * π)
notation `ℝ2π` := RealMod2π

namespace RealMod2π

noncomputable instance : HasOfNat ℝ2π := ⟨WIP⟩
noncomputable instance : HasAdd ℝ2π := ⟨WIP⟩
noncomputable instance : HasNeg ℝ2π := ⟨WIP⟩
noncomputable instance : HasSub ℝ2π := ⟨WIP⟩
noncomputable instance : HasPi ℝ2π := ⟨WIP⟩

end RealMod2π

def RealModπ : Type := Quot (λ (x y : ℝ) => x % π = y % π)
notation `ℝπ` := RealModπ

namespace RealModπ

noncomputable instance : HasOfNat ℝπ := ⟨WIP⟩
noncomputable instance : HasAdd ℝπ := ⟨WIP⟩
noncomputable instance : HasNeg ℝπ := ⟨WIP⟩
noncomputable instance : HasSub ℝπ := ⟨WIP⟩

end RealModπ
