import Geo.Background.List

namespace Array

universe u
variable {α : Type u}

def allP (xs : Array α) (p : α → Prop) : Prop :=
xs.toList.allP p


end Array
