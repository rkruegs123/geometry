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

abbrev PReal : Type := { x : ℝ // x > 0 }
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

abbrev NNReal : Type := { x : ℝ // x ≥ 0 }
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

abbrev RealMod2π := { x : ℝ // x ≥ 0 ∧ x < 2 * π }
notation `ℝ2π` := RealMod2π

namespace RealMod2π

-- Warning: these operations are not the same as for ℝ

noncomputable instance : HasOfNat ℝ2π := ⟨WIP⟩
noncomputable instance : HasAdd ℝ2π := ⟨WIP⟩
noncomputable instance : HasNeg ℝ2π := ⟨WIP⟩
noncomputable instance : HasSub ℝ2π := ⟨WIP⟩
noncomputable instance : HasPi ℝ2π := ⟨WIP⟩
noncomputable instance : HasLess ℝ2π := ⟨WIP⟩
noncomputable instance : HasLessEq ℝ2π := ⟨WIP⟩

noncomputable def divNat : ℝ2π → Nat → ℝ2π := WIP

end RealMod2π

abbrev RealModπ : Type := { x : ℝ // x ≥ 0 ∧ x < π }

notation `ℝπ` := RealModπ

namespace RealModπ

-- Warning: these operations are not the same as for ℝ

noncomputable instance : HasOfNat ℝπ := ⟨WIP⟩
noncomputable instance : HasAdd ℝπ := ⟨WIP⟩
noncomputable instance : HasNeg ℝπ := ⟨WIP⟩
noncomputable instance : HasSub ℝπ := ⟨WIP⟩
noncomputable instance : HasLess ℝπ := ⟨WIP⟩
noncomputable instance : HasLessEq ℝπ := ⟨WIP⟩

noncomputable def divNat : ℝπ → Nat → ℝπ := WIP

end RealModπ
