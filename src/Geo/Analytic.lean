import Geo.Background.Real
import Geo.Background.List
import Geo.Background.Vec
import Geo.Background.Set
import Geo.Background.Tuple

/-
Currently, we do not require NDGs in the constructions.
We will experiment with requiring them only for the theorems about the constructions,
and perhaps auto-generating them from the theorem statements.

So far I have found the `HasOn` typeclass to be convenient because of all the helper functions,
but so far the other typeclasses have mostly just preempted the ⟨⟩ notation without much benefit.
-/

namespace Geo

structure Point : Type := (x y : ℝ)

noncomputable instance : Inhabited Point := Inhabited.mk ⟨0, 0⟩ -- check with daniel

namespace Point

noncomputable def add (p₁ p₂ : Point) : Point := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩
noncomputable def sub (p₁ p₂ : Point) : Point := ⟨p₁.x - p₂.x, p₁.y - p₂.y⟩

noncomputable instance : HasAdd Point := ⟨add⟩
noncomputable instance : HasSub Point := ⟨sub⟩

noncomputable def dot (p₁ p₂ : Point) : ℝ :=
p₁.x * p₂.x + p₁.y * p₂.y

end Point

namespace Analytic

noncomputable def det₂ (a b c d : ℝ) : ℝ :=
a * d - b * c

noncomputable def det₃ (a b c d e f g h i : ℝ) : ℝ :=
a * det₂ e f h i - b * det₂ d f g i + c * det₂ d e g h

variables (a b c d e f : Point)

noncomputable def sqdist : ℝ := (a.x - b.x)^2 + (a.y - b.y)^2
noncomputable def dist   : ℝ := Real.sqrt $ sqdist a b
noncomputable def sarea2 : ℝ := (det₃ a.x a.y 1 b.x b.y 1 c.x c.y 1) -- twice the signed area
noncomputable def sprod  : ℝ := Point.dot (a - b) (c - b)

noncomputable def midp   : Point := ⟨a.x + b.x / 2, a.y + b.y / 2⟩

noncomputable def coll : Prop := sarea2 a b c = 0
noncomputable def para : Prop := (a.x - b.x) * (c.y - d.y) - (a.y - b.y) * (c.x - d.x) = 0
noncomputable def perp : Prop := (a.x - b.x) * (c.x - d.x) + (a.y - b.y) * (c.y - d.y) = 0

noncomputable def deg2π (degrees : ℝ) : ℝ2π := ⟨((π : ℝ) * (degrees / 180)) % (2 * π), WIP⟩
noncomputable def degπ  (degrees : ℝ) : ℝπ  := ⟨((π : ℝ) * (degrees / 180)) % π, WIP⟩

noncomputable def eqangle : Prop :=
sarea2 a b c * sprod d e f = sarea2 d e f * sprod a b c

axiom sqdistGe0 : sqdist a b ≥ 0
axiom distGe0   : dist a b ≥ 0

end Analytic

end Geo
