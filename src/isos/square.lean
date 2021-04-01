import .id

-- sq(x) = x²
def sq (A) := A × A

namespace sq
-- sq(x) = x²
def fseq_iso {A} : sq A ≃ fseq 2 A :=
begin
  apply (_ ⋆ iso.func_left fin.two_iso.inv),
  apply (_ ⋆ iso.mul_func₁),
  apply iso.mul id.one_iso id.one_iso
end

-- x² = Σ n:ℕ, δ(2,n) xⁿ
def ogf_iso {A} : sq A ≃ ogf (delta 2) A :=
fseq_iso ⋆ fseq.ogf_iso

instance : has_ogf sq :=
⟨delta 2, @ogf_iso⟩
end sq
