import .fseq_ogf

namespace one
-- 1 = Σ n:ℕ, δ(0,n) xⁿ
def ogf_iso {A} : 1 ≃ ogf (delta 0) A :=
fseq.one_iso⁻¹ ⋆ fseq.ogf_iso

instance : has_ogf₁ 1 :=
⟨delta 0, ogf_iso⟩
end one
