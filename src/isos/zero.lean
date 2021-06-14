import functors.generating

namespace zero
-- 0 = Σ n:ℕ, cₙ xⁿ
-- cₙ = {0, 0, 0, 0, 0, ...}
def ogf_iso {A} : 0 ≃ ogf (const 0) A :=
⟨λ x, pempty.rec _ x, λ x, begin
  have z : fin 0 := x.2.1,
  apply fin.elim0 z
end, --λ x, fin.elim0 x.2.1,
 λ x, pempty.rec _ x, λ x, begin
  have z : fin 0 := x.2.1,
  apply fin.elim0 z
 end⟩ --λ x, fin.elim0 x.2.1⟩

instance : has_ogf₁ 0 :=
⟨const 0, ogf_iso⟩
end zero
