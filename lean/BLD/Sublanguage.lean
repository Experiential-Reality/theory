/- BLD Calculus — Sublanguage Predicates

   Three fragments obtained by removing one constructor:
     LD = no Sum       (Link + Dimension only)
     BD = no Function  (Boundary + Dimension only)
     BL = no Product   (Boundary + Link only)

   Reference: bld-calculus.md Definitions 6.1–6.3
-/

import BLD.Basic

namespace Ty

/-- A type is in the LD fragment (no Sum constructor).
    Reference: bld-calculus.md Definition 6.1 -/
inductive IsLD : Ty → Prop where
  | unit : IsLD .unit
  | fn   {a b : Ty} : IsLD a → IsLD b → IsLD (.fn a b)
  | prod {n : Nat} {t : Ty} : IsLD t → IsLD (.prod n t)

/-- A type is in the BD fragment (no Function constructor).
    Reference: bld-calculus.md Definition 6.2 -/
inductive IsBD : Ty → Prop where
  | unit : IsBD .unit
  | sum  {a b : Ty} : IsBD a → IsBD b → IsBD (.sum a b)
  | prod {n : Nat} {t : Ty} : IsBD t → IsBD (.prod n t)

/-- A type is in the BL fragment (no n-Product for n ≥ 2).
    Reference: bld-calculus.md Definition 6.3 -/
inductive IsBL : Ty → Prop where
  | unit : IsBL .unit
  | sum  {a b : Ty} : IsBL a → IsBL b → IsBL (.sum a b)
  | fn   {a b : Ty} : IsBL a → IsBL b → IsBL (.fn a b)

end Ty
