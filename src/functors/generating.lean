-- Analytic combinatorics[1,2] is a wonderful subject for analyzing large
-- combinatorial structures using methods from complex analysis.
-- This is an attempt to formalize some of the ideas in Lean.
-- [1] https://aofa.cs.princeton.edu/home
-- [2] http://algo.inria.fr/flajolet/Publications/book.pdf

import data.iso
import data.fseq
import function
import isos.fseq
import functors.analytic

def perm (n) := fin n ≃ fin n
def orbit {n} (p : perm n) (a b : fin n) := ∃ k, iter p.1 k a = b
def factor {n} (p : perm n) := quot (orbit p)
def kcycles (k n) := Σ p : perm n, factor p ≃ fin k
def cyc (n : ℕ₁) := Σ' p : perm n.1, ∀ i, p.1 i = p.1 ⟨0, n.2⟩ + i

def ordered (n A) (a b : fseq n A) := a = b
def unordered (n A) (a b : fseq n A) := ∃ p : perm n, (a ∘ p.1) = b
def cyclic (n : ℕ₁) (A) (a b : fseq n.1 A) := ∃ p : cyc n, (a ∘ p.1.1) = b
def kcyclic (k n : ℕ₁) (A) (a b : fseq n.1 A) := ∃ p : kcycles k.1 n.1, (a ∘ p.1.1) = b
def dirichlet (k n : ℕ₁) (A) (a b : fseq n.1 A) := ∃ p : fin k.1 → cyc n, ∀ i, (a ∘ (p i).1.1) = b

-- fset(n,x) = xⁿ / n!
def fset (n A) := quot (unordered n A)

-- fsec(n,x) = xⁿ / n
def fsec (n A) := quot (cyclic n A)

-- Ordinary generating function
-- ogf(c,x) = Σ n:ℕ, cₙ xⁿ
def ogf (c : ℕ → ℕ) (X) :=
Σ n:ℕ, fin (c n) × fseq n X

-- Exponential generating function
-- egf(c,x) = Σ n:ℕ, cₙ xⁿ / n!
def egf (c : ℕ → ℕ) (A) :=
Σ n:ℕ, fin (c n) × fset n A

-- lgf(c,x) = Σ n:ℕ₁, cₙ xⁿ / n
def lgf (c : ℕ₁ → ℕ) (A) :=
Σ n:ℕ₁, fin (c n) × fsec n A

-- Dirichlet generating function
-- dgf(k,c,x) = Σ n:ℕ₁, cₙ xⁿ / nᵏ
def dgf (k : ℕ₁) (c : ℕ₁ → ℕ) (A) :=
Σ n:ℕ₁, fin (c n) × quot (dirichlet k n A)

def shape {N} (c : N → ℕ) := Σ n, fin (c n)
def size {N c} (x : @shape N c) := x.1

-- ogf(c) ↪ af(ordered, shape(c), size)
def lift_ogf {c A} (x : ogf c A) : af ordered (shape c) size A :=
⟨⟨x.1, x.2.1⟩, quot.mk _ x.2.2⟩

-- egf(c) ↪ af(unordered, shape(c), size)
def lift_egf {c A} (x : egf c A) : af unordered (shape c) size A :=
⟨⟨x.1, x.2.1⟩, x.2.2⟩

-- lgf(c) ↪ af₁(cyclic, shape(c), size)
def lift_lgf {c A} (x : lgf c A) : af₁ cyclic (shape c) size A :=
⟨⟨x.1, x.2.1⟩, x.2.2⟩

-- dgf(k,c) ↪ af₁(dirichlet(k), shape(c), size)
def lift_dgf {k c A} (x : dgf k c A) : af₁ (dirichlet k) (shape c) size A :=
⟨⟨x.1, x.2.1⟩, x.2.2⟩

class has_ogf (f : Type → Type) :=
(cf : ℕ → ℕ)
(iso {A} : f A ≃ ogf cf A)

class has_ogf₁ (A : Type) :=
(cf : ℕ → ℕ)
(iso : A ≃ ogf cf 1)

instance ogf_has_ogf₁ {f} [has_ogf f] : has_ogf₁ (f 1) :=
⟨has_ogf.cf f, has_ogf.iso⟩

namespace ogf
def cadd (a b : ℕ → ℕ) (n : ℕ) := a n + b n

def cmul (a b : ℕ → ℕ) (n : ℕ) := partial_sum (λ k, a k * b (n - k)) n

def add_iso {a b A} : ogf a A ⊕ ogf b A ≃ ogf (cadd a b) A :=
iso.sigma_add ⋆ iso.sigma_subst (λ n, iso.distr_right⁻¹ ⋆ iso.mul_left fin.add_iso)

-- Σ n:ℕ, cₙ xⁿ = c₀ + x Σ n:ℕ, cₙ₊₁ xⁿ
def foo_iso {c : ℕ → ℕ} {A} : (Σ n, fin (c n) × fseq n A) ≃ fin (c 0) ⊕ A × Σ n, fin (c (n+1)) × fseq n A :=
begin
  apply (ax₁ ⋆ _),
  apply (iso.add_left (iso.mul_right fseq.one_iso ⋆ iso.mul_one_right.inv) ⋆ _),
  apply iso.add_right,
  apply (_ ⋆ ax₂),
  apply iso.sigma_subst (λ n, _),
  apply (_ ⋆ iso.mul_assoc ⋆ iso.mul_comm),
  apply iso.mul_right,
  apply (_ ⋆ iso.mul_comm),
  apply fseq.cons_iso.inv
end

def mul_iso {a b A} : ogf a A × ogf b A ≃ ogf (cmul a b) A :=
sorry

def shape_iso {c} : ogf c 1 ≃ shape c :=
iso.sigma_subst (λ n, iso.mul_right fseq.one_iso₂ ⋆ iso.mul_one_right⁻¹)

instance {c A} [has_repr A] : has_repr (ogf c A) :=
{repr := λ x, "⟨" ++ repr x.1 ++ ", " ++ repr x.2 ++ "⟩"}
end ogf
