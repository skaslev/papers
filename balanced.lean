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

@[simp] lemma prod.mk.eta {α β} : Π {p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

@[reducible] def fins (k n : ℕ) := fin k → fin n

-- gⁿ(x) = Σ k:ℕ, nᵏ x^(k+1) = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- thrm gn_iso: ∀ n:ℕ, gⁿ(unit) = Σ k:ℕ, fins k n
-- => f(unit) = Σ n:ℕ, gⁿ(unit) = Σ n:ℕ, Σ k:ℕ, fins k n

def countG1 {α} : G α → ℕ
| (G.G0 x) := nat.zero
| (G.G1 x xs) := nat.succ (countG1 xs)

def append {α} : G α → G α → G α
| (G.G0 x) ys := G.G1 x ys
| (G.G1 x xs) ys := G.G1 x (append xs ys)

def join {α} : G (G α) → G α
| (G.G0 x) := x
| (G.G1 x xs) := append x (join xs)

def leafs {n α} (x : iter G n α) : G α :=
begin
  induction n with n ih generalizing α,
  { exact G.G0 x },
  { exact join (ih x) }
end

@[reducible] def Gnk (n k : ℕ) α := Σ' x : iter G n α, countG1 (leafs x) = k

@[reducible] def mkGnk {n : ℕ} {α} (x : iter G n α) : Σ k : ℕ, Gnk n k α :=
⟨countG1 (leafs x), x, rfl⟩

def push (n k : ℕ) {α} (a : α) : fin n × Gnk n k α → Gnk n (nat.succ k) α :=
sorry

def pull (n k : ℕ) {α} (a : α) : Gnk n (nat.succ k) α → fin n × Gnk n k α :=
sorry

def encode' {n k : ℕ} (x : fins k n) : Gnk n k unit :=
sorry

def decode' {n k : ℕ} (x : Gnk n k unit) : fins k n :=
sorry

def encode_decode' {n k : ℕ} (x : Gnk n k unit) : encode' (decode' x) = x :=
sorry

def decode_encode' {n k : ℕ} (x : fins k n) : decode' (encode' x) = x :=
sorry

def encode {n : ℕ} (x : Σ k : ℕ, fins k n) : iter G n unit :=
(encode' x.2).1

def decode {n : ℕ} (x : iter G n unit) : Σ k : ℕ, fins k n :=
let y := mkGnk x in ⟨y.1, decode' y.2⟩

def encode_decode {n : ℕ} (x : iter G n unit) : encode (decode x) = x :=
by simp [encode, decode, encode_decode']

def decode_encode {n : ℕ} (x : Σ k : ℕ, fins k n) : decode (encode x) = x :=
begin
  induction x with k x,
  dsimp [encode, decode],
  admit
end

def gn_iso (n : ℕ) : iso (iter G n unit) (Σ k : ℕ, fins k n) :=
⟨decode, encode, encode_decode, decode_encode⟩

def s_iso : iso (S G unit) (Σ n k : ℕ, fins k n) :=
⟨ λ s, ⟨s.1, (gn_iso s.1).f s.2⟩,
  λ s, ⟨s.1, (gn_iso s.1).g s.2⟩,
  by intros s; simp [(gn_iso s.1).gf],
  by intros s; simp [(gn_iso s.1).fg] ⟩

def f_iso : iso (F G unit) (Σ n k : ℕ, fins k n) :=
iso_comp (iso_inv sf_iso) s_iso