-- f(x) = x + f(g(x)) ↔ f(x) = Σ n:ℕ, gⁿ(x)
inductive F (g : Type → Type) : Type → Type 1
| F₀ : Π {α}, α → F α
| F₁ : Π {α}, F (g α) → F α

-- g(x) = x + x g(x) ↔ g(x) = x/(1-x) ↔ gⁿ(x) = x/(1-nx)
inductive G (α : Type) : Type
| G₀ : α → G
| G₁ : α → G → G

def iter {α} (g : α → α) : ℕ → α → α
| nat.zero := id
| (nat.succ n) := iter n ∘ g

def diter {β : Type → Type 1} {γ : Type → Type} (g : Π {α}, β (γ α) → β α) : Π (n : ℕ) {α}, β (iter γ n α) → β α
| nat.zero α := id
| (nat.succ n) α := g ∘ diter n

-- s(x) = Σ n:ℕ, gⁿ(x)
def S (g : Type → Type) (α : Type) := Σ n : ℕ, iter g n α

def from_s {g α} (x : S g α) : F g α :=
diter (@F.F₁ g) x.1 (F.F₀ g x.2)

def to_s {g α} (x : F g α) : S g α :=
F.rec (λ α a, ⟨nat.zero, a⟩) (λ α a ih, ⟨nat.succ ih.1, ih.2⟩) x

attribute [simp] function.comp

def to_s_from_s {g α} (x : S g α) : to_s (from_s x) = x :=
begin
  simp [to_s, from_s],
  induction x with n x,
  induction n with m ih generalizing α,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

def from_s_to_s {g α} (x : F g α) : from_s (to_s x) = x :=
begin
  simp [to_s, from_s],
  induction x with β x β x ih,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

structure {u v} iso (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x) (fg : Π x, f (g x) = x)

-- s(x) = f(x)
def sf_iso {g α} : iso (S g α) (F g α) :=
⟨from_s, to_s, to_s_from_s, from_s_to_s⟩

-- gⁿ(x) = Σ k:ℕ, nᵏ x^(k+1) = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- ⇒ gⁿ(1) = Σ k:ℕ, fin k → fin n
-- ⇒ f(1) = Σ n:ℕ, gⁿ(1) = Σ n:ℕ, Σ k:ℕ, fin k → fin n
