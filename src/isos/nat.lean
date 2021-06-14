import isos.id

namespace nat
-- ℕ = 1 + ℕ
def def_iso : ℕ ≃ 1 ⊕ ℕ :=
⟨λ x, nat.rec (sum.inl ()) (λ y ih, sum.inr y) x,
 λ x, sum.rec (λ y, 0) (λ y, y+1) x,
 λ x, begin induction x with x ih, repeat { refl } end,
 λ x, begin induction x, { induction x, refl }, refl end⟩

-- ℕ = Σ n:ℕ, 1
def ogf_iso : ℕ ≃ ogf (const 1) 1 :=
iso.sigma_one⁻¹ ⋆ iso.sigma_subst (λ n, iso.mul_one_left ⋆ (iso.mul fin.one_iso fseq.one_iso₂)⁻¹)

instance : has_ogf₁ ℕ :=
⟨const 1, ogf_iso⟩
end nat

namespace nats
-- ω^ω = ω ω^ω
def def_iso : ℕ → ℕ ≃ ℕ × (ℕ → ℕ) :=
iso.func_left nat.def_iso ⋆ iso.mul_func₁⁻¹ ⋆ iso.mul_left id.one_iso⁻¹

-- ω^ω = ωⁿ ω^ω
def fseq_iso {n} : ℕ → ℕ ≃ fseq n ℕ × (ℕ → ℕ) :=
begin
  induction n with n ih,
  { exact (iso.mul_one_left ⋆ iso.mul_left fseq.one_iso.inv) },
  apply (_ ⋆ iso.mul_assoc ⋆ iso.mul_left fseq.cons_iso),
  apply (_ ⋆ iso.mul_right ih),
  apply def_iso
end
end nats
