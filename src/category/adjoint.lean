import data.iso

-- Adjoint functors
-- bᶠ⁽ᵃ⁾ = g(b)ᵃ
def adj (f g : Type → Type) := Π A B, (f A → B) ≃ (A → g B)

notation f ` ⊣ ` g := adj f g

-- "Every monad arises from some adjunction — in fact, typically from many adjunctions"

-- The slogan is "Adjoint functors arise everywhere".
--     — Saunders Mac Lane, Categories for the Working Mathematician

namespace adj
-- xa ⊣ xᵃ
def curry (A : Type) : (λ x, x × A) ⊣ (λ x, A → x) :=
λ B C, iso.curry⁻¹
end adj
