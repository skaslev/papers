import data.fseq
import data.iso

-- Analytic functor
-- This is definition 1.2 from [3] but the relation r doesn't depend
-- on the index i, only on its size s(i)
-- [3] https://www.ms.u-tokyo.ac.jp/~ryu/papers/taa.ps
-- af(r,I,s,x) = Σ i:I, x^s(i) / r(s(i))
def af (r : Π n A, rel (fseq n A)) (I) (s : I → ℕ) (A) :=
Σ i:I, quot (r (s i) A)

def af₁ (r : Π (n:ℕ₁) A, rel (fseq n.1 A)) (I) (s : I → ℕ₁) (A) :=
Σ i:I, quot (r (s i) A)

def ext_rel₁ (r : Π (n:ℕ₁) A, rel (fseq n.1 A)) : Π n A, rel (fseq n A)
| 0 := λ A a b, true  -- `fseq 0 A` is a singleton type
| (n+1) := r ⟨n+1, nat.pos_of_ne_zero (nat.succ_ne_zero n)⟩

def ext_s₁ {I} (s : I → ℕ₁) (i : I) : ℕ := (s i).1

-- af₁(r,I,s) ↪ af(ext_rel₁(r), I, ext_s₁(s))
def lift_af₁ {r I s A} (x : af₁ r I s A) : af (ext_rel₁ r) I (ext_s₁ s) A :=
⟨x.1, eq.mp begin
  dsimp [ext_s₁],
  induction (s x.1) with n nh,
  induction n,
  { exact false.elim (nat.lt_irrefl 0 nh) },
  { simp [ext_rel₁] }
end x.2⟩

namespace af
def sadd {I₁ I₂} (s₁ : I₁ → ℕ) (s₂ : I₂ → ℕ) : I₁ ⊕ I₂ → ℕ :=
iso.mul_func₁.f (s₁, s₂)

def smul {I₁ I₂} (s₁ : I₁ → ℕ) (s₂ : I₂ → ℕ) (x : I₁ × I₂) : ℕ :=
s₁ x.1 + s₂ x.2

def add_iso {r I₁ I₂ s₁ s₂ A} : (af r I₁ s₁ A) ⊕ (af r I₂ s₂ A) ≃ af r (I₁ ⊕ I₂) (sadd s₁ s₂) A :=
⟨λ x, sum.rec (λ y, ⟨sum.inl y.1, y.2⟩) (λ y, ⟨sum.inr y.1, y.2⟩) x,
 λ x,
 begin
   induction x with x₁ x₂,
   induction x₁,
   { dsimp [sadd] at x₂,
     exact sum.inl ⟨x₁, x₂⟩ },
   { dsimp [sadd] at x₂,
     exact sum.inr ⟨x₁, x₂⟩ }
 end,
 λ x, by induction x; repeat { simp [prod.mk.eta] },
 λ x, by induction x with x₁ x₂; induction x₁; repeat { refl }⟩

def mul_iso {r I₁ I₂ s₁ s₂ A} : (af r I₁ s₁ A) × (af r I₂ s₂ A) ≃ af r (I₁ × I₂) (smul s₁ s₂) A :=
sorry
end af
