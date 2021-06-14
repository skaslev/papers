import data.fseq
import functors.generating

-- Geometric power series
-- geom(x) = Σ n:ℕ, xⁿ
def geom (A) := Σ n, fseq n A

namespace geom
-- geom(x) = 1 + x geom(x)
def lin_iso {A} : geom A ≃ 1 ⊕ A × (geom A) :=
ax₁ ⋆ iso.add fseq.one_iso (iso.sigma_subst (λ n, fseq.cons_iso⁻¹) ⋆ ax₂)

-- geom(x) = Σ n:ℕ, xⁿ
def ogf_iso {A} : geom A ≃ ogf (const 1) A :=
iso.sigma_subst (λ n, iso.mul_one_left ⋆ iso.mul_left fin.one_iso⁻¹)

instance : has_ogf geom :=
⟨const 1, @ogf_iso⟩
end geom
