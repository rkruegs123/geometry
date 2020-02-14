import Geo.Arith.CRing
import Geo.Arith.Field
import Geo.Background.Real

namespace Arith
namespace Test

open FExpr

abbrev x := atom 0
abbrev y := atom 1
abbrev z := atom 2

-- TODO: fix these examples
-- Normalize, assert numerators H-simplify to 1
def check0 (fe : FExpr) : IO Unit :=
if fe.norm.numer.toHExpr == 0
then IO.println "PASS"
else throw $ IO.userError (toString fe.norm.numer.toHExpr ++ " ≠ 0")

def checkF (fe : FExpr) : IO Unit :=
if ¬ (fe.norm.numer.toHExpr == 0)
then IO.println "PASS"
else throw $ IO.userError (toString fe.norm.numer.toHExpr ++ " = 0")

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
#eval check0 $ x / x - 1
#eval check0 $ x / y + y / x - x^2 / (x * y) - y^2 / (x * y)
#eval check0 $ x / (y + z) - y / (y + z) + (y - x) / (y + z)
#eval check0 $ x / (x / x) - x
#eval check0 $ x / (x / (x / x)) - 1
#eval check0 $ x / (x / (x / (x / x))) - x

#eval checkF $ x
#eval checkF $ x - x + 1
#eval checkF $ x - - y - x - y + x
#eval checkF $ x / x
#eval checkF $ x^2 / y^2 - 1
#eval checkF $ x^2 / (y^2 / (x + y + z)) - 1
#eval checkF $ x / (x + y) * (x / (x + (y + z)))

end Test
end Arith
