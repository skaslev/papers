-- f(x) = x + f(g(x)) ↔ f(x) = Σ n:ℕ, gⁿ(x)
inductive F (g : Type → Type) : Type → Type 1
| F₀ : Π {α}, α → F α
| F₁ : Π {α}, F (g α) → F α

-- g(x) = x + x g(x) ↔ g(x) = x/(1-x) ↔ gⁿ(x) = x/(1-nx)
inductive G α : Type
| G₀ : α → G
| G₁ : α → G → G

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

def sf_iso {g α} : iso (S g α) (F g α) :=
⟨from_s, to_s, to_s_from_s, from_s_to_s⟩

def iso_inv {α β} (i : iso α β) : iso β α :=
⟨i.g, i.f, i.fg, i.gf⟩

def iso_comp {α β γ} (i : iso α β) (j : iso β γ) : iso α γ :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩

@[simp] lemma prod.mk.eta {α β} : Π {p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

@[simp] def fiber {α β} (f : α → β) (y : β) := Σ' x, f(x) = y

@[simp] def iscontr α := Σ' x : α, Π y : α, x = y

structure {u v} eqv (α : Type u) (β : Type v) :=
(f : α → β) (h : Π y, iscontr (fiber f y))

def {u v} iso_eqv {α : Type u} {β : Type v} (i : iso α β) : eqv α β :=
⟨i.f, (λ y, ⟨⟨i.g y, i.fg y⟩, (λ ⟨x, h⟩, by simp [h.symm, i.gf])⟩)⟩

def {u v} eqv_iso {α : Type u} {β : Type v} (i : eqv α β) : iso α β :=
⟨i.f, (λ y, (i.h y).1.1),
begin
  intro,
  let y := i.f x,
  have b := (i.h y).1,
  have w := i.h (i.f x),
  induction w with fib con,
  have zz := con b,
  induction fib with xx gg,
  simp * at *,
  admit
end
, sorry⟩

@[reducible] def fins (n k : ℕ) := fin k → fin n

def from_fins {n : ℕ} (x : Σ k : ℕ, fins n k) : list (fin n) :=
begin
  induction x with k f,
  induction k with k ih,
  { exact [] },
  { exact f 0 :: ih (f ∘ fin.succ) }
end

def to_fins {n : ℕ} (x : list (fin n)) : Σ k : ℕ, fins n k :=
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
  simp [from_fins, to_fins],
  induction x with x xs ih,
  { refl },
  simp,
  -- rw ih,
  admit
end

def from_fins_fcontr {n : ℕ} : Π y, iscontr (fiber (@from_fins n) y) :=
begin
  intro y,
  have fib : fiber from_fins y := ⟨to_fins y, from_fins_to_fins y⟩,
  apply psigma.mk fib,
  intro fib2,
  induction fib with f h,
  induction fib2 with f2 h2,
  induction y with y ys ih,
  -- simp [fiber, from_fins] at fib fib2,

  simp [from_fins] at h h2,
  admit,
  admit
end

def fins_eqv (n : ℕ) : eqv (Σ k : ℕ, fins n k) (list (fin n))  :=
⟨from_fins, from_fins_fcontr⟩

def to_fins_from_fins {n : ℕ} (x : Σ k : ℕ, fins n k) : to_fins (from_fins x) = x :=
sorry

def fins_iso {n : ℕ} : iso (Σ k : ℕ, fins n k) (list (fin n)) :=
⟨from_fins, to_fins, to_fins_from_fins, from_fins_to_fins⟩

-- gⁿ(x) = Σ k:ℕ, nᵏ x^(k+1) = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- thrm gn_iso: ∀ n:ℕ, gⁿ(unit) = Σ k:ℕ, fins n k
-- => f(unit) = Σ n:ℕ, gⁿ(unit) = Σ n:ℕ, Σ k:ℕ, fins n k

def encode {n : ℕ} (x : list (fin n)) : iter G n unit :=
sorry

def decode {n : ℕ} (x : iter G n unit) : list (fin n) :=
sorry

def encode_decode {n : ℕ} (x : iter G n unit) : encode (decode x) = x :=
sorry

def decode_encode {n : ℕ} (x : list (fin n)) : decode (encode x) = x :=
sorry

def gl_iso {n : ℕ} : iso (iter G n unit) (list (fin n)) :=
⟨decode, encode, encode_decode, decode_encode⟩

def gn_iso {n : ℕ} : iso (iter G n unit) (Σ k : ℕ, fins n k) :=
iso_comp gl_iso (iso_inv fins_iso)

def s_iso : iso (S G unit) (Σ n k : ℕ, fins n k) :=
⟨λ s, ⟨s.1, gn_iso.f s.2⟩, λ s, ⟨s.1, gn_iso.g s.2⟩, by simp [gn_iso.gf], by simp [gn_iso.fg]⟩

def f_iso : iso (F G unit) (Σ n k : ℕ, fins n k) :=
iso_comp (iso_inv sf_iso) s_iso

def power (x : Type) : ℕ → Type
| 0 := unit
| 1 := x
| (n+2) := x × power (n+1)

def pseries (s : ℕ → ℕ) (x : Type) := Σ n : ℕ, fin (s n) × power x n