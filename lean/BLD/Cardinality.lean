/- BLD Calculus — Cardinality and Mode Count

   Cardinality: number of distinct closed values of a type.
   Reference: bld-calculus.md Proposition 7.2

   Mode count: structural dimensions (differs from cardinality for products).
   Reference: bld-calculus.md Definition 8.3
-/

import BLD.Basic

namespace Ty

/-- Cardinality of inhabitants of a type.

    |1|         = 1
    |τ₁ + τ₂|  = |τ₁| + |τ₂|
    |τ₁ → τ₂|  = |τ₂| ^ |τ₁|
    |Πₙ(τ)|    = |τ| ^ n
-/
def cardinality : Ty → Nat
  | .unit       => 1
  | .sum a b    => a.cardinality + b.cardinality
  | .fn a b     => b.cardinality ^ a.cardinality
  | .prod n t   => t.cardinality ^ n

/-- Structural mode count.

    μ(1)         = 1
    μ(τ₁ + τ₂)  = μ(τ₁) + μ(τ₂)
    μ(τ₁ → τ₂)  = μ(τ₂) ^ μ(τ₁)
    μ(Πₙ(τ))    = n × μ(τ)

    Differs from cardinality in the product case:
    cardinality counts inhabitants (|τ|^n),
    mode count counts structural dimensions (n × μ(τ)).
-/
def modeCount : Ty → Nat
  | .unit       => 1
  | .sum a b    => a.modeCount + b.modeCount
  | .fn a b     => b.modeCount ^ a.modeCount
  | .prod n t   => n * t.modeCount

end Ty
