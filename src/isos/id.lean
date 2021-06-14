import isos.fseq_ogf

namespace id
-- x = Σ n:ℕ, δ(1,n) xⁿ
def ogf_iso {A} : A ≃ ogf (delta 1) A :=
fseq.id_iso⁻¹ ⋆ fseq.ogf_iso

instance : has_ogf id :=
⟨delta 1, @ogf_iso⟩

-- x = 0 + 1 x
def linear {A} : A ≃ 0 ⊕ 1 × A :=
iso.mul_one_left ⋆ iso.add_zero_left

-- x = x¹
def one_iso {A} : A ≃ 1 → A :=
⟨λ x y, x,
 λ x, x (),
 λ x, rfl,
 λ x, funext (λ y, punit.rec rfl y)⟩
end id
