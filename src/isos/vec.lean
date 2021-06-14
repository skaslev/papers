import isos.geom
import isos.fseq_ogf

inductive vec (A : Type) : ℕ → Type
| nil : vec 0
| cons {n} : A → vec n → vec (n+1)

namespace vec
def def_iso₁ {A} : vec A 0 ≃ 1 :=
⟨λ x, (),
 λ x, vec.nil,
 λ x, match x with
 | vec.nil := rfl
 end,
 λ x, begin induction x, refl end⟩

def def_iso₂ {n A} : vec A (n+1) ≃ A × (vec A n) :=
⟨λ x, match x with
 | vec.cons h t := (h, t)
 end,
 λ x, vec.cons x.1 x.2,
 λ x, match x with
 | vec.cons h t := rfl
 end,
 λ x, by simp [def_iso₂._match_1]⟩

-- vec(x,n) = xⁿ
def fseq_iso {n A} : vec A n ≃ fseq n A :=
begin
  induction n with n ih,
  { exact (def_iso₁ ⋆ fseq.one_iso.inv) },
  apply (def_iso₂ ⋆ _),
  apply (_ ⋆ fseq.cons_iso),
  apply iso.mul_right,
  apply ih
end

-- Σ n:ℕ, vec(x,n) = Σ n:ℕ, xⁿ
def geom_iso {A} : (Σ n, vec A n) ≃ geom A :=
iso.sigma_subst (λ n, fseq_iso)

-- vec(x,n) = Σ k:ℕ, δ(n,k) xᵏ
def ogf_iso {n A} : vec A n ≃ ogf (delta n) A :=
fseq_iso ⋆ fseq.ogf_iso

-- Σ n:ℕ, vec(x,n) = Σ k:ℕ, xᵏ
def ogf_iso₁ {A} : (Σ n, vec A n) ≃ ogf (const 1) A :=
geom_iso ⋆ geom.ogf_iso
end vec
