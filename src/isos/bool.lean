import ..functors.generating

namespace bool
def def_iso : bool ≃ 1 ⊕ 1 :=
⟨λ x, bool.rec (sum.inl ()) (sum.inr ()) x,
 λ x, sum.rec (λ x, ff) (λ x, tt) x,
 λ x, begin induction x, repeat {simp} end,
 λ x, begin induction x, repeat {induction x, simp} end⟩

def cf : ℕ → ℕ
| 0 := 2
| _ := 0

def ogf_iso : bool ≃ ogf cf 1 :=
begin
  apply (def_iso ⋆ _),
  apply (_ ⋆ ax₁.inv),
  apply (_ ⋆ iso.add_left (iso.mul_one_right ⋆ iso.mul_right fseq.one_iso.inv)),
  apply iso.add_zero_right_subst fin.two_iso.inv _,
  apply iso.sigma_subst_zero (λ n, _),
  apply (iso.mul_left fin.zero_iso ⋆ _),
  apply iso.mul_zero_left.inv
end

instance : has_ogf₁ bool :=
⟨cf, ogf_iso⟩
end bool
