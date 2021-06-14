import functors.generating

namespace option
-- option(x) = 1 + x
def def_iso {A} : option A ≃ 1 ⊕ A :=
⟨λ x, option.rec (sum.inl ()) sum.inr x,
 λ x, sum.rec (λ _, option.none) option.some x,
 λ x, by induction x; repeat { simp },
 λ x, begin induction x, { induction x, simp }, simp end⟩

def cf (n : ℕ) : ℕ := ite (n < 2) 1 0

def cf_lemma {n} : cf (n + 2) = 0 :=
begin
  have h : ¬ n + 2 < 2 := nat.not_lt_zero n ∘ nat.lt_of_succ_lt_succ ∘ nat.lt_of_succ_lt_succ,
  simp [cf, if_neg h]
end

-- option(x) = Σ n:ℕ, cₙ xⁿ
-- where cₙ = {1, 1, 0, 0, 0, ...}
def ogf_iso {A} : option A ≃ ogf cf A :=
begin
  apply (def_iso ⋆ _),
  apply (_ ⋆ ax₁.inv),
  apply (_ ⋆ iso.add_left (iso.mul_one_left ⋆ iso.mul fin.one_iso.inv fseq.one_iso.inv)),
  apply iso.add_right,
  apply (_ ⋆ ax₁.inv),
  apply (_ ⋆ iso.add_left (iso.mul_one_left ⋆ iso.mul fin.one_iso.inv fseq.id_iso.inv)),
  apply (iso.add_zero_right ⋆ _),
  apply iso.add_right,
  simp [cf_lemma],
  apply (_ ⋆ iso.sigma_subst (λ n, iso.mul_zero_left ⋆ (@iso.mul_left _ _ (fseq (n + 2) A)) fin.zero_iso.inv)),
  apply iso.sigma_zero.inv
end

instance : has_ogf option :=
⟨cf, @ogf_iso⟩
end option
