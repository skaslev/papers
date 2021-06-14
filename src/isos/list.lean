import isos.nat
import isos.vec

namespace list
-- list(x) = 1 + x list(x) = 1/(1-x)
def def_iso {A} : list A ≃ 1 ⊕ A × (list A) :=
⟨λ x, list.rec (sum.inl ()) (λ h t ih, sum.inr (h, t)) x,
 λ x, sum.rec (λ y, []) (λ y, y.1 :: y.2) x,
 λ x, by induction x; repeat { simp },
 λ x, by induction x; { induction x, refl }; { simp }⟩

-- list(x) = Σ n:ℕ, vec(x,n)
def vec_iso {A} : list A ≃ Σ n, vec A n :=
⟨λ x, list.rec ⟨0, vec.nil⟩ (λ h t ih, ⟨ih.1+1, vec.cons h ih.2⟩) x,
 λ x, vec.rec [] (λ n h t ih, h :: ih) x.2,
 λ x, begin induction x with h t ih, { refl }, simp [ih] end,
 λ x, begin induction x with x₁ x₂, induction x₂ with n h t ih, { refl }, { simp [ih], rw ih } end⟩

def geom_iso {A} : list A ≃ geom A :=
vec_iso ⋆ vec.geom_iso

-- list(x) = Σ n:ℕ, cₙ xⁿ = Σ n:ℕ, xⁿ
-- cₙ = {1, 1, 1, 1, 1, ...}
def ogf_iso {A} : list A ≃ ogf (const 1) A :=
geom_iso ⋆ geom.ogf_iso

instance : has_ogf list :=
⟨const 1, @ogf_iso⟩

-- list(1) = ℕ
def nat_iso : list 1 ≃ ℕ :=
ogf_iso ⋆ nat.ogf_iso⁻¹
end list

namespace list_zero
-- list(0) = 1
def one_iso : list 0 ≃ 1 :=
⟨λ x, (),
 λ x, [],
 λ x, list.rec rfl (λ h t ih, pempty.rec _ h) x,
 isprop_one _⟩

def one_iso₁ : list 0 ≃ 1 :=
list.def_iso ⋆ iso.add_right iso.mul_zero_left⁻¹ ⋆ iso.add_zero_right⁻¹

def one_iso₂ : list 0 ≃ 1 :=
begin
  apply (list.def_iso ⋆ _),
  apply (iso.add_right iso.mul_zero_left.inv ⋆ _),
  apply iso.add_zero_right.inv
end
end list_zero
