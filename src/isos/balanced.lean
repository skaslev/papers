import .fins

-- Balanced Trees[4,5,6]
-- [4] https://github.com/skaslev/papers/blob/master/iterating.pdf
-- [5] https://github.com/skaslev/papers/blob/master/balanced.pdf
-- [6] https://github.com/skaslev/papers/blob/master/balanced-comb.pdf

-- f(x) = x + f(g(x)) ↔ f(x) = Σ n:ℕ, gⁿ(x)
inductive F (g : Type → Type) : Type → Type 1
| F₀ {A} : A → F A
| F₁ {A} : F (g A) → F A

-- s(x) = Σ n:ℕ, gⁿ(x)
def S (g : Type → Type) (A) := Σ n:ℕ, iter g n A

namespace S
def code {g A} (x : S g A) : F g A :=
diter (@F.F₁ g) x.1 (F.F₀ x.2)

def deco {g A} (x : F g A) : S g A :=
F.rec (λ A a, ⟨0, a⟩) (λ A a ih, ⟨ih.1+1, ih.2⟩) x

def deco_code {g A} (x : S g A) : deco (code x) = x :=
begin
  simp [deco, code],
  induction x with n x,
  induction n with m ih generalizing A,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

def code_deco {g A} (x : F g A) : code (deco x) = x :=
begin
  simp [deco, code],
  induction x with B x B x ih,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

-- s(g,x) = f(g,x)
def f_iso {g A} : S g A ≃ F g A :=
⟨code, deco, deco_code, code_deco⟩
end S

-- g(x) = x + x g(x) ↔ g(x) = x/(1-x) ↔ gⁿ(x) = x/(1-nx)
inductive G (A : Type) : Type
| G₀ : A → G
| G₁ : A → G → G

namespace G
-- g(x) = x + x g(x)
def def_iso {A} : G A ≃ A ⊕ A × (G A) :=
⟨λ x, G.rec sum.inl (λ h t ih, sum.inr (h, t)) x,
 λ x, sum.rec G.G₀ (λ y, G.G₁ y.1 y.2) x,
 λ x, by induction x; repeat { refl },
 λ x, by induction x; repeat { simp }⟩

-- g(x) = x (1 + g(x))
def mul_iso {A} : G A ≃ A × (1 ⊕ G A) :=
def_iso ⋆ iso.distr_one_left

-- g(x) = x/(1-x)
def list_iso {A} : G A ≃ A × (list A) :=
⟨λ x, G.rec (λ h, (h, [])) (λ h t ih, (ih.1, h :: ih.2)) x,
 λ x, list.rec (G.G₀ x.1) (λ h t ih, G.G₁ h ih) x.2,
 λ x, begin induction x with h h t ih, { refl }, { simp [ih] } end,
 λ x, begin induction x with x₁ x₂, induction x₂ with h t ih, { refl }, simp [ih] end⟩

-- 1 + g(x) = 1/(1-x)
def list_iso₁ {A} : 1 ⊕ G A ≃ list A :=
iso.add_right list_iso ⋆ list.def_iso⁻¹

def cf (n : ℕ) := ite (n = 0) 0 1

def cf_lemma : cf = ogf.cmul (delta 1) (const 1) :=
begin
  funext n,
  by_cases n=0,
  { simp [h, cf, delta, const, ogf.cmul, partial_sum, if_neg nat.zero_ne_one] },
  simp [h, cf, delta, const, ogf.cmul, partial_sum],
  induction n with n ih,
  { exact false.elim (h rfl) },
  simp [partial_sum],
  by_cases n=0,
  { rename h g,
    simp [g, partial_sum, if_neg nat.zero_ne_one] },
  { rename h g,
    rw ←ih g,
    have h₁ : ¬n+1=1 := λ x, false.elim (g (nat.add_right_cancel x)),
    rw if_neg h₁ }
end

-- g(x) = Σ n:ℕ, xⁿ⁺¹ = Σ n:ℕ, cₙ xⁿ
-- cₙ = {0, 1, 1, 1, 1, 1, ...}
def ogf_iso {A} : G A ≃ ogf cf A :=
eq.mp (by rw cf_lemma) (list_iso ⋆ iso.mul id.ogf_iso list.ogf_iso ⋆ ogf.mul_iso)

-- g(1) = ℕ
def nat_iso : G 1 ≃ ℕ :=
list_iso ⋆ iso.mul_one_left⁻¹ ⋆ list.nat_iso
end G

namespace Gⁿ
-- gⁿ(x) = x + n x gⁿ(x)
def lin_iso {n A} : iter G n A ≃ A ⊕ (fin n × A) × (iter G n A) :=
begin
  induction n with n ih generalizing A,
  { exact (iso.add_zero_right ⋆ iso.add_right (iso.mul_zero_left ⋆ iso.mul_left (iso.mul_zero_left ⋆ iso.mul_left fin.zero_iso.inv))) },
  apply (ih ⋆ _),
  apply (iso.add_right (iso.mul_left iso.mul_comm ⋆ iso.mul_assoc.inv) ⋆ _),
  apply (iso.distr_one_left ⋆ _),
  apply (iso.mul_left G.mul_iso ⋆ iso.mul_assoc.inv ⋆ _),
  apply (_ ⋆ iso.add_right (iso.mul_assoc ⋆ iso.mul_left iso.mul_comm)),
  apply (_ ⋆ iso.distr_one_left.inv),
  apply iso.mul_right,
  apply (iso.distr_one_right.inv ⋆ iso.add_assoc.inv ⋆ _),
  apply iso.add_right,
  apply (_ ⋆ iso.mul_left fin.add_one_iso),
  apply (_ ⋆ iso.add_comm ⋆ iso.distr_one_right),
  apply iso.add_right,
  apply (iso.distr_one_left.inv ⋆ _),
  apply (iso.add_right (iso.mul_assoc ⋆ iso.mul_left iso.mul_comm.inv) ⋆ _),
  apply ih.inv
end

-- gⁿ(x) = x/(1-nx)
def list_iso {n A} : iter G n A ≃ A × list (fin n × A) :=
sorry

-- n gⁿ(x) = g(nx)
def gn_iso {n A} : fin n × iter G n A ≃ G (fin n × A) :=
iso.mul_right list_iso ⋆ iso.mul_assoc ⋆ G.list_iso⁻¹

-- m gⁿᵐ(x) = gⁿ(mx)
def gnm_iso {n m A} : fin m × iter G (n*m) A ≃ iter G n (fin m × A) :=
begin
  apply (_ ⋆ list_iso.inv),
  apply (iso.mul_right list_iso ⋆ _),
  apply (iso.mul_assoc ⋆ _),
  apply iso.mul_right,
  exact iso.map (iso.mul_left fin.mul_iso.inv ⋆ iso.mul_assoc.inv)
end

-- n gⁿᵐ(x) = gᵐ(nx)
def gmn_iso {n m A} : fin n × iter G (n*m) A ≃ iter G m (fin n × A) :=
begin rw nat.mul_comm, exact gnm_iso end

-- gⁿ(1) = 1/(1-n)
def list_iso₁ {n} : iter G n 1 ≃ list (fin n) :=
list_iso ⋆ iso.mul_one_left⁻¹ ⋆ iso.map iso.mul_one_right⁻¹

-- gⁿ(x) = Σ k:ℕ, nᵏ xᵏ⁺¹ = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- ⇒ gⁿ(1) = Σ k:ℕ, fin k → fin n
-- ⇒ f(1) = Σ n:ℕ, gⁿ(1) = Σ n:ℕ, Σ k:ℕ, fin k → fin n
def fins_iso {n} : iter G n 1 ≃ Σ k, fin k → fin n :=
list_iso₁ ⋆ fins.list_iso⁻¹

def cf (n k : ℕ) : ℕ := ite (k = 0) 0 (n^(k-1))

def cf_lemma₁ (n : ℕ) : cf n 0 = 0 :=
by simp [cf]

def cf_lemma₂ (n k : ℕ) : cf n (k+1) = n^k :=
by simp [cf, if_neg (nat.succ_ne_zero k)]

-- gⁿ(x) = Σ k:ℕ, nᵏ xᵏ⁺¹ = Σ k:ℕ, cₖ xᵏ
-- cₙ = {0, 1, n, n², n³, ..., nᵏ⁻¹, ...}
def ogf_iso {n A} : iter G n A ≃ ogf (cf n) A :=
begin
  apply (list_iso ⋆ iso.mul_right list.geom_iso ⋆ _),
  apply (_ ⋆ ax₁.inv),
  rw cf_lemma₁,
  apply (_ ⋆ iso.add_zero_left ⋆ iso.add_left (iso.mul_zero_left ⋆ iso.mul_left fin.zero_iso.inv)),
  apply (ax₂.inv ⋆ _),
  apply iso.sigma_subst (λ k, _),
  apply (_ ⋆ iso.mul_assoc ⋆ iso.mul_comm ⋆ iso.mul_right fseq.cons_iso),
  apply iso.mul_right,
  apply (_ ⋆ iso.mul_comm),
  apply (iso.mul_func₂.inv ⋆ _),
  apply iso.mul_left,
  rw cf_lemma₂,
  apply fin.pow_iso
end

-- gⁿ(1) = Σ k:ℕ, nᵏ
def ogf_iso₁ {n} : iter G n 1 ≃ ogf (fins.cf n) 1 :=
fins_iso ⋆ fins.ogf_iso
end Gⁿ

-- ζₛ(k) = Σ n:ℕ, nᵏ
def ζₛ (k : ℕ) := Σ n, fin k → fin n

namespace SG
-- s(g,1) = Σ n k:ℕ, nᵏ
def fins_iso : S G 1 ≃ Σ n k, fin k → fin n :=
iso.sigma_subst (λ n, Gⁿ.fins_iso)

-- s(g,x) = Σ n:ℕ, x/(1-nx)
def list_iso {A} : S G A ≃ Σ n, A × list (fin n × A) :=
iso.sigma_subst (λ n, Gⁿ.list_iso)

-- s(g,1) = Σ n:ℕ, 1/(1-n)
def list_iso₁ : S G 1 ≃ Σ n, list (fin n) :=
fins_iso ⋆ iso.sigma_subst (λ n, fins.list_iso)

-- s(g,1) = Σ k:ℕ, ζₛ(k)
def zeta_iso : S G 1 ≃ Σ k, ζₛ k :=
fins_iso ⋆ iso.sigma_swap
end SG

namespace FG
-- f(g,1) = Σ n:ℕ, Σ k:ℕ, nᵏ
def fins_iso : F G 1 ≃ Σ n k, fin k → fin n :=
S.f_iso⁻¹ ⋆ SG.fins_iso

-- f(g,x) = Σ n:ℕ, x list(nx)
def list_iso {A} : F G A ≃ Σ n, A × list (fin n × A) :=
S.f_iso⁻¹ ⋆ SG.list_iso

-- f(g,1) = Σ n:ℕ, list(n)
def list_iso₁ : F G 1 ≃ Σ n, list (fin n) :=
S.f_iso⁻¹ ⋆ SG.list_iso₁

-- f(g,1) = Σ k:ℕ, ζₛ(k)
def zeta_iso : F G 1 ≃ Σ k, ζₛ k :=
S.f_iso⁻¹ ⋆ SG.zeta_iso
end FG

-- From Generatingfunctionology[7] pg. 18
-- B₀(x) = 1, ∀ k>0:
-- Bₖ(x) = x Bₖ₋₁(x) + k x Bₖ(x)
-- ⇒ Bₖ(x) = x/(1-kx) Bₖ₋₁(x)
-- [7] https://www.math.upenn.edu/~wilf/gfologyLinked2.pdf
inductive B (A : Type) : ℕ → Type
| B₀ : B 0
| B₁ {k} : A → (B k) → B (k+1)
| B₂ {k} : A → fin (k+1) → B (k+1) → B (k+1)
