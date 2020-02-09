import Geo.Background.Real
import Geo.Background.Set

/-
Currently, we do not require NDGs in the constructions.
We will experiment with requiring them only for the theorems about the constructions,
and perhaps auto-generating them from the theorem statements.

So far I have found the `HasOn` typeclass to be convenient because of all the helper functions,
but so far the other typeclasses have mostly just preempted the ⟨⟩ notation without much benefit.
-/

namespace Geo

structure Point : Type := (x y : ℝ)

class HasOn (α : Type) := (on : Point → α → Prop)
def on {α : Type} [HasOn α] : Point → α → Prop := HasOn.on

section
variables {α β : Type} [HasOn α] [HasOn β]

def intersectAt (x : α) (y : β) : Set Point := λ p => on p x ∧ on p y
def intersectAt₂ (x : α) (y : β) (p avoid : Point) : Prop := intersectAt x y p ∧ p ≠ avoid
def intersect (x : α) (y : β) : Prop := Exists (intersectAt x y)
def allIntersectAt (xs : List α) : Set Point := λ p => xs.allP (on p)
def allIntersect (xs : List α) : Prop := Exists (allIntersectAt xs)
def tangentAt (x : α) (y : β) : Set Point := unique (intersectAt x y)
def tangent (x : α) (y : β) : Prop := Exists (tangentAt x y)
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

protected def on (p : Point) (l : Line) : Prop := SKIP -- ARITH

instance : HasOn Line := ⟨Line.on⟩
noncomputable def reflectPL (p : Point) (l : Line) : Point := SKIP -- ARITH
noncomputable def reflectLL (l₁ l₂ : Line) : Line := SKIP -- ARITH
noncomputable instance ReflectPL : HasReflect Point Line := ⟨reflectPL⟩
noncomputable instance ReflectLL : HasReflect Line Line := ⟨reflectLL⟩

end Line

noncomputable def coll : Point → Point → Point → Prop := SKIP
noncomputable def foot (p : Point) (l : Line) : Point := SKIP -- ARITH
noncomputable def perpTo (p q : Point) : Point := SKIP -- ARITH

def para (l₁ l₂ : Line) : Prop := SKIP
def perp (l₁ l₂ : Line) : Prop := SKIP

structure Seg : Type := (src dst : Point)

namespace Seg

protected def on (p : Point) (l : Seg) : Prop := SKIP -- (on line & btw)
instance : HasOn Seg := ⟨Seg.on⟩

def toLine (l : Seg) : Line := ⟨l.src, l.dst⟩
instance : HasCoe Seg Line := ⟨toLine⟩

protected noncomputable def ulen (l : Seg) : ℝ≥ := SKIP -- ARITH
noncomputable instance : HasLength Seg := ⟨Seg.ulen⟩

protected noncomputable def midp (l : Seg) : Point := SKIP -- ARITH
noncomputable instance : HasMidpoint Seg := ⟨Seg.midp⟩

end Seg

noncomputable def perpBis (l : Seg) : Line := ⟨midp l, perpTo (midp l) l.dst⟩

structure Ray : Type := (src dst : Point)

namespace Ray

protected def on (p : Point) (l : Ray) : Prop := SKIP -- (on line & btw)
instance : HasOn Ray := ⟨Ray.on⟩

def toLine (l : Ray) : Line := ⟨l.src, l.dst⟩
instance : HasCoe Ray Line := ⟨toLine⟩

end Ray

structure Circle : Type := (origin : Point) (radius : ℝ₊)

namespace Circle

protected def on (p : Point) (Γ : Circle) : Prop := SKIP -- ARITH
instance : HasOn Circle := ⟨Circle.on⟩

protected def inside (p : Point) (Γ : Circle) : Prop := SKIP -- ARITH
instance : HasInside Circle := ⟨Circle.inside⟩

protected noncomputable def uarea (Γ : Circle) : ℝ≥ := SKIP -- ARITH
noncomputable instance : HasUnsignedArea Circle := ⟨Circle.uarea⟩

end Circle

noncomputable def cycl (ps : List Point) : Prop :=
Exists (λ (Γ : Circle) => ps.allP (flip on Γ))

structure Arc (Γ : Circle) : Type := (src dst avoid : Point)

namespace Arc

variable {Γ : Circle}

protected def on (p : Point) (arc : Arc Γ) : Prop := SKIP -- ARITH
instance: HasOn (Arc Γ) := ⟨Arc.on⟩

protected noncomputable def ulen (arc : Arc Γ) : ℝ≥ := SKIP -- ARITH
noncomputable instance : HasLength (Arc Γ) := ⟨Arc.ulen⟩

protected noncomputable def midp (arc : Arc Γ) : Point := SKIP -- ARITH
noncomputable instance : HasMidpoint (Arc Γ) := ⟨Arc.midp⟩

end Arc

def isChord (Γ : Circle) (l : Seg) : Prop := on l.src Γ ∧ on l.dst Γ

structure Triple (α : Type) : Type := (A B C : α)

namespace Triple

variables {α β : Type}
def map (f : α → β) : Triple α → Triple β
| ⟨A, B, C⟩ => ⟨f A, f B, f C⟩

instance : Functor Triple := { map := @map }

def cycle : Triple α → Triple α
| ⟨A, B, C⟩ => ⟨B, C, A⟩

def cycles (t : Triple α) : Triple (Triple α) :=
⟨t, t.cycle, t.cycle.cycle⟩

def cmap (f : Triple α → β) (t : Triple α) : Triple β :=
f <$> t.cycles

-- TODO: much more abstract typeclass?
def any (p : α → Prop) : Triple α → Prop
| ⟨A, B, C⟩ => p A ∨ p B ∨ p C

def all (p : α → Prop) : Triple α → Prop
| ⟨A, B, C⟩ => p A ∧ p B ∧ p C

end Triple

open Triple (cmap any all)

noncomputable def uangle : Triple Point → ℝ2π := SKIP
noncomputable def dangle : Triple Point → ℝπ  := SKIP

def Triangle : Type := Triple Point

namespace Triangle

protected def on : Point → Triangle → Prop := SKIP
instance : HasOn Triangle := ⟨Triangle.on⟩

protected def inside : Point → Triangle → Prop := SKIP
instance : HasInside Triangle := ⟨Triangle.inside⟩

protected noncomputable def uarea : Triangle → ℝ₊ := SKIP
noncomputable instance : HasUnsignedArea Triangle := ⟨Triangle.uarea⟩

protected noncomputable def sarea : Triangle → ℝ := SKIP
noncomputable instance : HasSignedArea Triangle := ⟨Triangle.sarea⟩

def sides : Triangle → Triple Seg
| ⟨A, B, C⟩ => ⟨⟨B, C⟩, ⟨C, A⟩, ⟨A, B⟩⟩

noncomputable def sideLengths (t : Triangle) : Triple ℝ≥ :=
ulen <$> sides t

def esides : Triangle → Triple Line
| ⟨A, B, C⟩ => ⟨⟨B, C⟩, ⟨C, A⟩, ⟨A, B⟩⟩

noncomputable def uangles (t : Triangle) : Triple ℝ2π :=
uangle <$> t.cycles

noncomputable def dangles (t : Triangle) : Triple ℝπ  :=
dangle <$> t.cycles

noncomputable def altitudes : Triangle → Triple Line :=
cmap $ λ t => ⟨t.A, foot t.A ⟨t.B, t.C⟩⟩

noncomputable def medians : Triangle → Triple Line :=
cmap $ λ t => ⟨t.A, midp (Seg.mk t.B t.C)⟩

noncomputable def circumcenter  : Triangle → Point := SKIP
noncomputable def incenter      : Triangle → Point := SKIP
noncomputable def orthocenter   : Triangle → Point := SKIP
noncomputable def centroid      : Triangle → Point := SKIP
noncomputable def excenters     : Triangle → Triple Point := SKIP

noncomputable def circumcircle  : Triangle → Circle := SKIP
noncomputable def incircle      : Triangle → Circle := SKIP
noncomputable def excircles     : Triangle → Triple Circle := SKIP

noncomputable def circumradius   : Triangle → ℝ₊ := SKIP
noncomputable def inradius       : Triangle → ℝ₊ := SKIP
noncomputable def exradii        : Triangle → Triple ℝ₊ := SKIP

noncomputable def pedalTriangle  : Triangle → Point → Triangle := SKIP

noncomputable def orthicTriangle (t : Triangle) : Triangle :=
pedalTriangle t t.orthocenter

noncomputable def medialTriangle (t : Triangle) : Triangle :=
pedalTriangle t t.circumcenter

noncomputable def ceviansThrough (t : Triangle) (p : Point) : Triple Line := SKIP

-- Awkward
def isCevian (t : Triangle) (l : Seg) : Prop :=
any (λ (t : Triangle) => t.A = l.src ∧ on l.dst t.esides.A) t.cycles

def isAcute (t : Triangle)     : Prop := SKIP
def isScalene (t : Triangle)   : Prop := SKIP
def isIsosceles (t : Triangle) : Prop := SKIP

end Triangle

end Geo
