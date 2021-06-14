import functors.generating

namespace fseq
-- xᵏ = Σ n:ℕ, δ(k,n) xⁿ
def ogf_iso {k A} : fseq k A ≃ ogf (delta k) A :=
⟨λ x, ⟨k, (⟨0, by simp [delta, nat.zero_lt_succ]⟩, x)⟩,
 λ x, dite (x.1=k) (λ h, eq.mp (by rw h) x.2.2) (λ h, begin have z : fin 0 := eq.mp (by simp [delta, if_neg h]) x.2.1, exact fin.elim0 z end),
 λ x, by simp; refl,
 λ x,
 begin
  induction x with n x,
  induction x with c x,
  dsimp,
  by_cases n = k,
  { simp [dif_pos h],
    dsimp [delta, if_pos h] at c,
    congr,
    repeat { rw ←h },
    { induction c with c c_h,
      induction c with c ih,
      { sorry },
      { simp [delta, if_pos h] at c_h,
        exact false.elim (nat.not_lt_zero _ (nat.lt_of_succ_lt_succ c_h)) }},
    { apply eq_rec_heq }},
  { simp [delta, h] at c,
    exact fin.elim0 c }
 end⟩

instance {n} : has_ogf (fseq n) :=
⟨delta n, @ogf_iso n⟩
end fseq
