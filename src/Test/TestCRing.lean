import Geo.Arith.CRing
import Geo.Background.Real

namespace Arith
namespace Test

open HExpr (horner hornerAux int)
open CRExpr

abbrev x := atom 0
abbrev y := atom 1
abbrev z := atom 2

def check0 (cr : CRExpr) : IO Unit :=
if (cr.toHExpr == 0)
then IO.println "PASS"
else throw $ IO.userError (toString cr.toHExpr ++ " ≠ 0")

#eval check0 0
#eval check0 $ 0 + 0
#eval check0 $ 0 + 0 + 0
#eval check0 $ 1 - 1
#eval check0 $ 1 - 1 + 2 - 2
#eval check0 $ x^2 - x*x
#eval check0 $ x^3 - x*x*x
#eval check0 $ x^4 - x*x*x*x
#eval check0 $ x^2 * x^3 - x^5
#eval check0 $ x^2 * (x^3 + 1) - x^5 - x^2
#eval check0 $ (x + y) * x^2 * (x^3 + 1) - (x^6 + x^3 + y * x^5 + y * x^2)
#eval check0 $ (x + y)^2 - x^2 - y^2 - 2 * x * y
#eval check0 $ (x + y + z)^2 - x^2 - y^2 - z^2 - 2 * x * y - 2 * y * z - 2 * x * z
#eval check0 $ x - x
#eval check0 $ x^2 - x*x
#eval check0 $ - (x + x) + 2 * x
#eval check0 $ - (x + x - 2 * x)
#eval check0 $ - ((x + y)^2) + (x^2 + 2*x*y + y^2)
#eval check0 $ - ((x + y)^2) + (x^2 + 2*x*y + y^2)
#eval check0 $ - ((x + y)^2) - - (x^2 + 2*x*y + y^2)
#eval check0 $ - (- ((x + y + z)^2) - - - - (x^2 + y^2 + z^2 + 2 * x * y + 2 * y * z + 2 * x * z))
#eval check0 $ ((x + 1) * y) - (x * y + 1 * y)
#eval check0 $ x^2 * (x + 1) * y - (x^3 * y + 1 * y * x^2)
#eval check0 $ x - - y - x - y

end Test
end Arith
