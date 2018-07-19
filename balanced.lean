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

def iter2 {γ : Type → Type} (g : Π {α}, α → γ α) : Π (n : ℕ) {α}, α → iter γ n α
| nat.zero α := id
| (nat.succ n) α := iter2 n ∘ g

def diter {β : Type → Type 1} {γ : Type → Type} (g : Π {α}, β (γ α) → β α) : Π (n : ℕ) {α}, β (iter γ n α) → β α
| nat.zero α := id
| (nat.succ n) α := g ∘ diter n

-- s(x) = Σ n:ℕ, gⁿ(x)
def S (g : Type → Type) (α : Type) := Σ n : ℕ, iter g n α

-- f(x) = s(x)
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

namespace iso
def inv {α β} (i : iso α β) : iso β α :=
⟨i.g, i.f, i.fg, i.gf⟩

def comp {α β γ} (i : iso α β) (j : iso β γ) : iso α γ :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩
end iso

def sf_iso {g α} : iso (S g α) (F g α) :=
⟨from_s, to_s, to_s_from_s, from_s_to_s⟩

-- @[simp] lemma prod.mk.eta {α β} : Π {p : α × β}, (p.1, p.2) = p
-- | (a, b) := rfl

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

@[reducible] def fins (k n : ℕ) := fin k → fin n

def fins_0_n {n : ℕ} : fins 0 n := fin.elim0
def elim_fins_kp1_0 {k : ℕ} (f : fins (k+1) 0) : empty := fin.elim0 (f 0)

def f0 {k n : ℕ} (x : fin n × fins k n) : fins (k+1) n
| ⟨0, h⟩ := x.1
| ⟨y+1, h⟩ := x.2 ⟨y, nat.lt_of_succ_lt_succ h⟩

def f1 {k n : ℕ} (f : fins (k+1) n) : fin n × fins k n := 
⟨f 0, f ∘ fin.succ⟩

def from_fins {n : ℕ} : (Σ k : ℕ, fins k n) → list (fin n)
| ⟨0, f⟩ := []
| ⟨l+1, f⟩ := f 0 :: from_fins ⟨l, f ∘ fin.succ⟩

def to_fins {n : ℕ} : list (fin n) → Σ k : ℕ, fins k n
| [] := ⟨0, fin.elim0⟩
| (x::xs) := let ⟨l, f⟩ := to_fins xs in ⟨l+1, f0 ⟨x,f⟩⟩

def to_fins2 {n : ℕ} (x : list (fin n)) : Σ k : ℕ, fins k n :=
begin
  induction x with x xs ih,
  { exact ⟨nat.zero, fin.elim0⟩ },
  { exact ⟨ih.1.succ, λ k,
    begin
      induction k with k k_lt,
      induction k with k ih2,
      { exact x },
      { exact ih2 (nat.lt_of_succ_lt k_lt) }
    end⟩ }
end

def from_fins_to_fins {n : ℕ} (x : list (fin n)) : from_fins (to_fins x) = x :=
begin
  induction x with x xs ih,
  { refl },
  -- simp [],
  -- simp [from_fins, to_fins],
  dsimp [to_fins, to_fins._match_1],
  -- rw ←ih,
  -- unfold to_fins._match_1,
  -- rw ih,
  admit
end

def to_fins_from_fins {n : ℕ} (x : Σ k : ℕ, fins k n) : to_fins (from_fins x) = x :=
begin
  induction x with k f,
  induction k,
  -- exact fin.elim0,
  simp [from_fins, to_fins],
  funext,
  admit, admit
end

def fins_iso {n : ℕ} : iso (Σ k : ℕ, fins k n) (list (fin n)) :=
⟨from_fins, to_fins, to_fins_from_fins, from_fins_to_fins⟩

-- gⁿ(x) = Σ k:ℕ, nᵏ x^(k+1) = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- thrm gn_iso: ∀ n:ℕ, gⁿ(unit) = Σ k:ℕ, fins k n
-- => f(unit) = Σ n:ℕ, gⁿ(unit) = Σ n:ℕ, Σ k:ℕ, fins k n

def encode {n : ℕ} (x : list (fin n)) : iter G n unit :=
begin
  induction x with x xs ih,
  { exact iter2 @G.G₀ n unit.star },
  { admit }
end

def decode {n : ℕ} (x : iter G n unit) : list (fin n) :=
sorry

def encode_decode {n : ℕ} (x : iter G n unit) : encode (decode x) = x :=
sorry

def decode_encode {n : ℕ} (x : list (fin n)) : decode (encode x) = x :=
sorry

def gl_iso {n : ℕ} : iso (iter G n unit) (list (fin n)) :=
⟨decode, encode, encode_decode, decode_encode⟩

def gn_iso {n : ℕ} : iso (iter G n unit) (Σ k : ℕ, fins k n) :=
gl_iso.comp fins_iso.inv

def s_iso : iso (S G unit) (Σ n k : ℕ, fins k n) :=
⟨λ s, ⟨s.1, gn_iso.f s.2⟩, λ s, ⟨s.1, gn_iso.g s.2⟩, by simp [gn_iso.gf], by simp [gn_iso.fg]⟩

def f_iso : iso (F G unit) (Σ n k : ℕ, fins k n) :=
sf_iso.inv.comp s_iso

def power (x : Type) : ℕ → Type
| 0 := unit
| 1 := x
| (n+2) := x × power (n+1)

def pseries (s : ℕ → ℕ) (x : Type) := Σ n : ℕ, fin (s n) × power x n