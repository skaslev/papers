-- f(x) = x + f(g(x)) ↔ f(x) = Σ n:ℕ, gⁿ(x)
inductive F (g : Type → Type) : Type → Type 1
| F0 : Π {α}, α → F α
| F1 : Π {α}, F (g α) → F α

-- g(x) = x + x g(x) ↔ g(x) = x/(1-x) ↔ gⁿ(x) = x/(1-nx)
inductive G α : Type
| G0 : α → G
| G1 : α → G → G

def iter {α} (g : α → α) : ℕ → α → α
| nat.zero := id
| (nat.succ n) := iter n ∘ g

def diter {β : Type → Type 1} {γ : Type → Type} (g : Π {α}, β (γ α) → β α) : Π (n : ℕ) {α}, β (iter γ n α) → β α
| nat.zero α := id
| (nat.succ n) α := g ∘ diter n

-- s(x) = Σ n:ℕ, gⁿ(x)
def S g α := Σ n : ℕ, iter g n α

-- f(x) = s(x)
def from_s {g α} (x : S g α) : F g α :=
diter (@F.F1 g) x.1 (F.F0 g x.2)

def to_s {g α} (x : F g α) : S g α :=
F.rec (λ α a, ⟨0, a⟩) (λ α a ih, ⟨nat.succ ih.1, ih.2⟩) x

attribute [simp] function.comp

def to_s_from_s {g α} (x : S g α) : to_s (from_s x) = x :=
begin
  simp [to_s, from_s],
  induction x with n x,
  induction n with m ih generalizing α,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih x }
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

def sf_iso {g α} : iso (S g α) (F g α) :=
⟨from_s, to_s, to_s_from_s, from_s_to_s⟩

def iso_inv {α β} : iso α β → iso β α
| ⟨f, g, gf, fg⟩ := ⟨g, f, fg, gf⟩

def iso_comp {α β γ} : iso α β → iso β γ → iso α γ
| ⟨f₀, g₀, gf₀, fg₀⟩ ⟨f₁, g₁, gf₁, fg₁⟩ :=
⟨f₁ ∘ f₀, g₀ ∘ g₁, by simp [gf₁, gf₀], by simp [fg₀, fg₁]⟩

def fins (k n : nat) := fin k → fin n

-- gⁿ(x) = Σ k:ℕ, nᵏ x^(k+1) = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- thrm gn_iso: ∀ n:ℕ, gⁿ(unit) = Σ k:ℕ, fins k n
-- => f(unit) = Σ n:ℕ, gⁿ(unit) = Σ n:ℕ, Σ k:ℕ, fins k n

def gn_iso (n:ℕ) : iso (iter G n unit) (Σ k:ℕ, fins k n) :=
sorry

def f_iso : iso (F G unit) (Σ n k:ℕ, fins k n) :=
begin
  constructor,
  {
    intros,
  },

end