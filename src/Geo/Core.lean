import Geo.Background.Real
import Geo.Background.List
import Geo.Background.Vec
import Geo.Background.Set
import Geo.Background.Tuple
import Geo.Geo.Analytic

/-
Currently, we do not require NDGs in the constructions.
We will experiment with requiring them only for the theorems about the constructions,
and perhaps auto-generating them from the theorem statements.

So far I have found the `HasOn` typeclass to be convenient because of all the helper functions,
but so far the other typeclasses have mostly just preempted the ⟨⟩ notation without much benefit.
-/

namespace Geo

class HasOn (α : Type) := (on : Point → α → Prop)
def on {α : Type} [HasOn α] : Point → α → Prop := HasOn.on

class HasInOrderOn (α : Type) := (inOrderOn: List Point → α → Prop)
def inOrderOn {α : Type} [HasInOrderOn α] : List Point → α → Prop := HasInOrderOn.inOrderOn


section
variables {α β : Type} [HasOn α] [HasOn β]

def allOn (x : α) (ps : List Point) : Prop := ps.allP (flip on x)

def intersectAt (x : α) (y : β) : Set Point := λ p => on p x ∧ on p y
def intersectAtt₂ (x : α) (y : β) (p₁ p₂ : Point) : Prop := intersectAt x y p₁ ∧ intersectAt x y p₂ ∧ p₁ ≠ p₂
def intersect (x : α) (y : β) : Prop := Exists (intersectAt x y)

def allIntersectAt (xs : List α) : Set Point := λ p => xs.allP (on p)
def allIntersect (xs : List α) : Prop := Exists (allIntersectAt xs)

def allIntersectAt₂ (xs : List α) (ys : List β) : Set Point :=
λ p => xs.allP (on p) ∧ ys.allP (on p)
def allIntersect₂ (xs : List α) (ys : List β) : Prop := 
Exists (allIntersectAt₂ xs ys)

def intersectAtMany (x : α) (y : β) (ps : List Point) : Prop := ps.allP (λ p => intersectAt x y p)

def tangentAt (x : α) (y : β) : Set Point := unique (intersectAt x y)
def tangent (x : α) (y : β) : Prop := Exists (tangentAt x y)

-- ryankrue: is there a better way to do this?
-- ryankrue: note that this is ordered (e.g., the second element is the second point of intersection)
--noncomputable def intersectionPoints (x : α) (y : β) : List Point := WIP
--noncomputable def numIntersections (x : α) (y : β) : Nat := (intersectionPoints x y).length


end

class HasInside (α : Type) := (inside : Point → α → Prop)
def inside {α : Type} [HasInside α] : Point → α → Prop := HasInside.inside

class HasReflect (α β : Type) : Type := (reflect : α → β → α)
def reflect {α β : Type} [HasReflect α β] : α → β → α := HasReflect.reflect

class HasUnsignedArea (α : Type) : Type := (uarea : α → ℝ≥)
def uarea {α : Type} [HasUnsignedArea α] : α → ℝ≥ := HasUnsignedArea.uarea

class HasSignedArea (α : Type) : Type := (sarea : α → ℝ)
def sarea {α : Type} [HasSignedArea α] : α → ℝ  := HasSignedArea.sarea

class HasLength (α : Type) := (ulen : α → ℝ≥)
def ulen {α : Type} [HasLength α] : α → ℝ≥ := HasLength.ulen

class HasMidpoint (α : Type) := (midp : α → Point)
def midp {α : Type} [HasMidpoint α] : α → Point := HasMidpoint.midp

structure Line : Type := (p₁ p₂ : Point)

namespace Line

def same (l₁ l₂ : Line) : Prop := WIP

def wf : Line → Prop
| ⟨a, b⟩ => a ≠ b

protected def on (p : Point) : Line → Prop
| ⟨a, b⟩ => a ≠ b ∧ Analytic.coll p a b -- TODO: bundle NDGs like this?
instance : HasOn Line := ⟨Line.on⟩

protected def inOrderOn (ps : List Point) : Line → Prop := WIP
instance : HasInOrderOn Line := ⟨Line.inOrderOn⟩

noncomputable def reflectPL (p : Point) (l : Line) : Point := WIP -- ARITH
noncomputable def reflectLL (l₁ l₂ : Line) : Line := WIP -- ARITH
noncomputable instance ReflectPL : HasReflect Point Line := ⟨reflectPL⟩
noncomputable instance ReflectLL : HasReflect Line Line := ⟨reflectLL⟩

noncomputable def buildPara (p : Point) (l : Line) : Line := WIP -- build a line passing through p parallel to l

end Line

noncomputable def coll : Point → Point → Point → Prop := Analytic.coll
noncomputable def foot (p : Point) (l : Line) : Point := WIP -- ARITH
noncomputable def perpTo (p q : Point) : Point := WIP -- ARITH

def para (l₁ l₂ : Line) : Prop :=
l₁.wf ∧ l₂.wf ∧ Analytic.para l₁.p₁ l₁.p₂ l₂.p₁ l₂.p₂

def perp (l₁ l₂ : Line) : Prop :=
l₁.wf ∧ l₂.wf ∧ Analytic.perp l₁.p₁ l₁.p₂ l₂.p₁ l₂.p₂

structure Seg : Type := (src dst : Point)

namespace Seg

protected def on (p : Point) (l : Seg) : Prop := WIP -- (on line & btw)
instance : HasOn Seg := ⟨Seg.on⟩

protected def inOrderOn (ps : List Point) : Seg → Prop := WIP
instance : HasInOrderOn Seg := ⟨Seg.inOrderOn⟩

def toLine (l : Seg) : Line := ⟨l.src, l.dst⟩
instance : HasCoe Seg Line := ⟨toLine⟩

protected noncomputable def ulen (l : Seg) : ℝ≥ :=
⟨Analytic.dist l.src l.dst, Analytic.distGe0 _ _⟩
noncomputable instance : HasLength Seg := ⟨Seg.ulen⟩

protected noncomputable def midp (l : Seg) : Point :=
Analytic.midp l.src l.dst
noncomputable instance : HasMidpoint Seg := ⟨Seg.midp⟩

def cong (l₁ l₂ : Seg) : Prop := ulen l₁ = ulen l₂

end Seg

noncomputable def perpBis (l : Seg) : Line := ⟨midp l, perpTo (midp l) l.dst⟩

structure Ray : Type := (src dst : Point)

namespace Ray

protected def on (p : Point) (l : Ray) : Prop := WIP
instance : HasOn Ray := ⟨Ray.on⟩

protected def inOrderOn (ps : List Point) : Ray → Prop := WIP
instance : HasInOrderOn Ray := ⟨Ray.inOrderOn⟩

def toLine (l : Ray) : Line := ⟨l.src, l.dst⟩
instance : HasCoe Ray Line := ⟨toLine⟩

end Ray

structure Circle : Type := (origin : Point) (radius : ℝ₊)

namespace Circle

protected def on (p : Point) (Γ : Circle) : Prop :=
Γ.radius = ⟨Analytic.dist p Γ.origin, Analytic.distGe0 _ _⟩
instance : HasOn Circle := ⟨Circle.on⟩

protected def inOrderOn (ps : List Point) : Circle → Prop := WIP
instance : HasInOrderOn Circle := ⟨Circle.inOrderOn⟩

protected def inside (p : Point) (Γ : Circle) : Prop :=
Γ.radius > ⟨Analytic.dist p Γ.origin, Analytic.distGe0 _ _⟩

instance : HasInside Circle := ⟨Circle.inside⟩

noncomputable def diameter (Γ : Circle) : ℝ₊ := Γ.radius * 2
def isDiameter (p₁ p₂ : Point) (Γ : Circle) : Prop :=
ulen (Seg.mk p₁ p₂) = Γ.diameter
def isDiameter₂ (p₁ p₂ : Point) (Γ : Circle) : Prop :=
on p₁ Γ ∧ on p₂ Γ ∧ isDiameter p₁ p₂ Γ

protected noncomputable def uarea (Γ : Circle) : ℝ≥ :=
π * Γ.radius^2

noncomputable instance : HasUnsignedArea Circle := ⟨Circle.uarea⟩

noncomputable def lineTangentAtP (Γ : Circle) (p : Point) : Line := WIP
noncomputable def lineTangentAtP₂ (c : Circle) (p : Point) : on p c → Line := WIP
noncomputable def lineTangentAtP₃ (O P : Point) : Line := WIP

protected noncomputable def buildOP (origin p : Point) : Circle := WIP
protected noncomputable def buildPPP (p₁ p₂ p₃ : Point) : Circle := WIP
protected noncomputable def buildDiam (diameter : Seg) : Circle := WIP

noncomputable def commonExtTangents (Γ₁ Γ₂ : Circle) : List Line := WIP

end Circle

noncomputable def cycl (ps : List Point) : Prop :=
Exists (λ (Γ : Circle) => allOn Γ ps)

structure Arc (Γ : Circle) : Type := (src dst avoid : Point)

namespace Arc

variable {Γ : Circle}

protected def on (p : Point) (arc : Arc Γ) : Prop := WIP -- ARITH
instance: HasOn (Arc Γ) := ⟨Arc.on⟩

protected def inOrderOn (ps : List Point) : Arc Γ → Prop := WIP
instance : HasInOrderOn (Arc Γ) := ⟨Arc.inOrderOn⟩ -- ryankrue: potentially don't need depending on Circle representation

protected noncomputable def ulen (arc : Arc Γ) : ℝ≥ := WIP -- ARITH
noncomputable instance : HasLength (Arc Γ) := ⟨Arc.ulen⟩

protected noncomputable def midp (arc : Arc Γ) : Point := WIP -- ARITH
noncomputable instance : HasMidpoint (Arc Γ) := ⟨Arc.midp⟩

noncomputable def buildMinor (Γ : Circle) : Point → Point → Arc Γ := WIP
noncomputable def buildMajor (Γ : Circle) : Point → Point → Arc Γ := WIP

end Arc

def isChord (Γ : Circle) (l : Seg) : Prop := on l.src Γ ∧ on l.dst Γ

open Triple (cmap any all)

def Angle : Type := Triple Point

noncomputable def uangle : Angle → ℝ2π := WIP
noncomputable def dangle : Angle → ℝπ  := WIP

namespace Angle

noncomputable def bisector : Angle → Line := WIP
def isBisector (l : Line) (ang : Angle) : Prop := WIP 

def isRight : Angle → Prop := WIP

end Angle

def Triangle : Type := Triple Point

namespace Triangle

protected def mk (A B C : Point) : Triangle := ⟨A, B, C⟩

protected noncomputable def buildLLL (l₁ l₂ l₃ : Line) : Triangle := WIP

protected def on : Point → Triangle → Prop := WIP

instance : HasOn Triangle := ⟨Triangle.on⟩

protected def inside : Point → Triangle → Prop := WIP
instance : HasInside Triangle := ⟨Triangle.inside⟩

protected noncomputable def uarea : Triangle → ℝ₊ := WIP
noncomputable instance : HasUnsignedArea Triangle := ⟨Triangle.uarea⟩

protected noncomputable def sarea : Triangle → ℝ := WIP
noncomputable instance : HasSignedArea Triangle := ⟨Triangle.sarea⟩

def sides : Triangle → Triple Seg
| ⟨A, B, C⟩ => ⟨⟨B, C⟩, ⟨C, A⟩, ⟨A, B⟩⟩

noncomputable def sideLengths (tri : Triangle) : Triple ℝ≥ :=
ulen <$> sides tri

def esides : Triangle → Triple Line
| ⟨A, B, C⟩ => ⟨⟨B, C⟩, ⟨C, A⟩, ⟨A, B⟩⟩

-- RK: note that tri.cycles returns angles in the following order [B, C, A]
noncomputable def angles (tri : Triangle) : Triple Angle :=
match tri.cycles with ⟨B, C, A⟩ => ⟨A, B, C⟩

def isRight (tri : Triangle) : Prop :=
Triple.any Angle.isRight tri.angles

noncomputable def uangles (tri : Triangle) : Triple ℝ2π :=
uangle <$> tri.angles

noncomputable def dangles (tri : Triangle) : Triple ℝπ  :=
dangle <$> tri.angles

noncomputable def altitudes : Triangle → Triple Line :=
cmap $ λ tri => ⟨tri.A, foot tri.A ⟨tri.B, tri.C⟩⟩

noncomputable def medians : Triangle → Triple Line :=
cmap $ λ tri => ⟨tri.A, midp (Seg.mk tri.B tri.C)⟩

noncomputable def circumcenter  : Triangle → Point := WIP
noncomputable def incenter      : Triangle → Point := WIP
noncomputable def orthocenter   : Triangle → Point := WIP
noncomputable def centroid      : Triangle → Point := WIP
noncomputable def excenters     : Triangle → Triple Point := WIP

noncomputable def circumcircle  : Triangle → Circle := WIP
noncomputable def incircle      : Triangle → Circle := WIP

-- ryankrue: excircles.A ought to be the excircle across from X in a triangle ⟨X, Y, Z⟩
noncomputable def excircles     : Triangle → Triple Circle := WIP

noncomputable def circumradius   : Triangle → ℝ₊ := WIP
noncomputable def inradius       : Triangle → ℝ₊ := WIP
noncomputable def exradii        : Triangle → Triple ℝ₊ := WIP

noncomputable def pedalTriangle  : Triangle → Point → Triangle := WIP

noncomputable def orthicTriangle (tri : Triangle) : Triangle :=
pedalTriangle tri tri.orthocenter

noncomputable def medialTriangle (tri : Triangle) : Triangle :=
pedalTriangle tri tri.circumcenter

noncomputable def ceviansThrough (tri : Triangle) (p : Point) : Triple Line := WIP

-- Awkward
def cevian (tri : Triangle) (l : Seg) : Prop :=
any (λ (tri : Triangle) => tri.A = l.src ∧ on l.dst tri.esides.A) tri.cycles

def acute (tri : Triangle)       : Prop := WIP
def scalene (tri : Triangle)     : Prop := WIP
def isosceles (tri : Triangle)   : Prop := WIP
def equilateral (tri : Triangle) : Prop := WIP

end Triangle

open Quadruple (cmap any all)

def Quadrilateral : Type := Quadruple Point

namespace Quadrilateral

protected def mk (A B C D : Point) : Quadrilateral := ⟨A, B, C, D⟩

protected def on : Point → Quadrilateral → Prop := WIP

instance : HasOn Quadrilateral := ⟨Quadrilateral.on⟩

protected def inside : Point → Quadrilateral → Prop := WIP
instance : HasInside Quadrilateral := ⟨Quadrilateral.inside⟩

protected noncomputable def uarea : Quadrilateral → ℝ₊ := WIP
noncomputable instance : HasUnsignedArea Quadrilateral := ⟨Quadrilateral.uarea⟩

protected noncomputable def sarea : Quadrilateral → ℝ := WIP
noncomputable instance : HasSignedArea Quadrilateral := ⟨Quadrilateral.sarea⟩

def sides : Quadrilateral → Quadruple Seg
| ⟨A, B, C, D⟩ => ⟨⟨A, B⟩, ⟨B, C⟩, ⟨C, D⟩, ⟨D, A⟩⟩

noncomputable def sideLengths (quad : Quadrilateral) : Quadruple ℝ≥ :=
ulen <$> sides quad

def esides : Quadrilateral → Quadruple Line
| ⟨A, B, C, D⟩ => ⟨⟨A, B⟩, ⟨B, C⟩, ⟨C, D⟩, ⟨D, A⟩⟩

noncomputable def angles : Quadrilateral → Quadruple Angle
| ⟨A, B, C, D⟩ => ⟨⟨D, A, B⟩, ⟨A, B, C⟩, ⟨B, C, D⟩, ⟨C, D, A⟩⟩

noncomputable def uangles (quad : Quadrilateral) : Quadruple ℝ2π :=
uangle <$> quad.angles

noncomputable def dangles (quad : Quadrilateral) : Quadruple ℝπ  :=
dangle <$> quad.angles

-- could either be that there exists a circle with all points on it,
-- or could define a circle with three of the points and ensure that the other two are on it
-- (this way we don't have an existential)
def cyclic   : Quadrilateral → Prop := WIP
def convex   : Quadrilateral → Prop := WIP
def regular  : Quadrilateral → Prop := WIP
def harmonic : Quadrilateral → Prop := WIP

def parallelogram (quad : Quadrilateral) : Prop :=
convex quad ∧ para quad.esides.A quad.esides.C ∧ para quad.esides.B quad.esides.D

def trapezoid (quad : Quadrilateral) : Prop :=
convex quad ∧ (para quad.esides.A quad.esides.C ∨ para quad.esides.B quad.esides.D)

end Quadrilateral

/-
Triangle and Quadrilateral could be made Polygons.
For now, we keep it this way for convienence,
and only use Polygon for n ≥ 5.
-/
structure Polygon (n : Nat) : Type := (ps : Vec Point n)

namespace Polygon

variables {n : Nat}

noncomputable def buildPs (ps : List Point) : Polygon (ps.length) := WIP

def vertices (pgon : Polygon n) : Vec Point n := pgon.ps

noncomputable def sides (pgon : Polygon n)  : Vec Seg n := WIP
noncomputable def sideLengths (pgon : Polygon n)  : Vec ℝ≥ n := WIP
def equalSides (pgon : Polygon n) : Prop := pgon.sideLengths.allEq
noncomputable def esides (pgon : Polygon n) : Vec Line n := WIP
noncomputable def angles (pgon : Polygon n) : Vec Angle n := WIP

def convex : Polygon n → Prop := WIP
def regular : Polygon n → Prop := WIP

end Polygon

open Polygon

/- UNCOMMENT FOR >2 types intersecting
namespace WithInst

def ListWithInst (ϕ : ∀ (α : Type), Type) : Type 1 := List (Sigma (λ γ => ϕ γ × γ))
def allIntersectAt₂ (xs : ListWithInst HasOn) : Set Point := λ p => xs.allP (λ ⟨α, ⟨inst, x⟩⟩ => on p x)
def allIntersect₂ (xs : ListWithInst HasOn) : Prop := Exists (allIntersectAt₂ xs)

def intersectElem {α : Type} [inst : HasOn α] (x : α) : Sigma (λ γ => HasOn γ × γ) := ⟨α, ⟨inst, x⟩⟩
--def examplePolymorphicSpec (a b c : Point) : Prop := 
allIntersect₂ [intersectElem $ Seg.mk a b, intersectElem $ Line.mk a c]

end WithInst
-/

end Geo
