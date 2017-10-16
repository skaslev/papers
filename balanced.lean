-- f(x) = x + f(g(x))
inductive F (g : Type → Type) : Type → Type 1
| F0 : Π {α}, α → F α
| F1 : Π {α}, F (g α) → F α

inductive G α : Type
| G0 : α → G
| G1 : α → G → G

def iter {α} (g : α → α) : ℕ → α → α
| nat.zero := id
| (nat.succ n) := iter n ∘ g

def diter {β : Type → Type 1} {γ : Type → Type} (g : Π {α}, β (γ α) → β α) : Π (n : ℕ) {α}, β (iter γ n α) → β α
| nat.zero α := id
| (nat.succ n) α := g ∘ diter n

def S g α := Σ n : ℕ, iter g n α

-- f(x) = Σ n:ℕ, gⁿ(x)
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