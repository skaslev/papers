def ℕ₁ := Σ' n:ℕ, n > 0

def iter {α} (g : α → α) : ℕ → α → α
| 0 := id
| (n+1) := iter n ∘ g

def perm (n) := Σ' p : fin n → fin n, function.bijective p
def part (k n) := Σ' p : fin n → fin k, function.surjective p
def inorb {n} (p : perm n) (a b : fin n) := ∃ s, iter p.1 s a = b
def factor {n} (p : perm n) : Σ' k (q : part k n), ∀ a b, q.1 a = q.1 b ↔ inorb p a b := sorry
def kcycles (k n) := Σ' p : perm n, (factor p).1 = k

-- fseq n x = xⁿ
def fseq (n : ℕ) (α : Type) := fin n → α

def ordered (n α) (a b : fseq n α) := a = b
def unordered (n α) (a b : fseq n α) := ∃ p : perm n, (a ∘ p.1) = b
def kcyclic (k n : ℕ₁) (α) (a b : fseq n.1 α) := ∃ p : kcycles k.1 n.1, (a ∘ p.1.1) = b
def cyclic := kcyclic ⟨1, nat.zero_lt_succ 0⟩

-- fset n x = xⁿ / n!
def fset (n α) := quot (unordered n α)

-- fsec n x = xⁿ / n
def fsec (n α) := quot (cyclic n α)

-- fsed k n x = xⁿ / nᵏ
def fsed (k n α) := quot (kcyclic k n α)

-- ogf c x = Σ n:ℕ, cₙ xⁿ
def ogf (c : ℕ → ℕ) (α) :=
Σ n : ℕ, fin (c n) × fseq n α

-- egf c x = Σ n:ℕ, cₙ xⁿ / n!
def egf (c : ℕ → ℕ) (α) :=
Σ n : ℕ, fin (c n) × fset n α

-- cgf c x = Σ n:ℕ₁, cₙ xⁿ / n
def cgf (c : ℕ₁ → ℕ) (α) :=
Σ n : ℕ₁, fin (c n) × fsec n α

-- dgf c k x = Σ n:ℕ₁, cₙ xⁿ / nᵏ
def dgf (c : ℕ₁ → ℕ) (k α) :=
Σ n : ℕ₁, fin (c n) × fsed k n α

-- ζ k x = Σ n:ℕ₁, xⁿ / nᵏ
def ζ (k) := dgf (λ _, 1) k

def rel (α) := α → α → Prop

-- Analytic functor
-- This is definition 1.2 from [1] but the relation r doesn't depend
-- on the index i, only on its size s(i)
-- [1] https://www.ms.u-tokyo.ac.jp/~ryu/papers/taa.ps
-- af r s x = Σ i:I, x^s(i) / r(s(i))
def af (r : Π n α, rel (fseq n α)) (I) (s : I → ℕ) (α) :=
Σ i : I, quot (r (s i) α)

def shape (c : ℕ → ℕ) := Σ n, fin (c n)
def size {c} (x : shape c) := x.1

-- ogf c ↪ af ordered (shape c) size
def lift_ogf {c α} (x : ogf c α) : af ordered (shape c) size α :=
⟨⟨x.1, x.2.1⟩, quot.mk _ x.2.2⟩

-- egf c ↪ af unordered (shape c) size
def lift_egf {c α} (x : egf c α) : af unordered (shape c) size α :=
⟨⟨x.1, x.2.1⟩, x.2.2⟩

inductive ℕω
| fin : ℕ → ℕω
| inf : ℕω

def iseq (α : Type) := ℕ → α

def seqω : ℕω → Type → Type
| (ℕω.fin n) := fseq n
| ℕω.inf := iseq

def afω (r : Π n α, rel (seqω n α)) (I) (s : I → ℕω) (α) :=
Σ i : I, quot (r (s i) α)

def ext_relω (r : Π n α, rel (fseq n α)) (q : Π α, rel (iseq α)) : Π n α, rel (seqω n α)
| (ℕω.fin n) := r n
| ℕω.inf := q

-- af r I s ↪ afω (ext_relω r q) I (ℕω.fin ∘ s)
def lift_af {r I s α} (q : Π α, rel (iseq α)) (x : af r I s α) : afω (ext_relω r q) I (ℕω.fin ∘ s) α :=
x

def af₁ (r : Π (n:ℕ₁) α, rel (fseq n.1 α)) (I) (s : I → ℕ₁) (α) :=
Σ i : I, quot (r (s i) α)

def ext_rel₁ (r : Π (n:ℕ₁) α, rel (fseq n.1 α)) : Π (n:ℕ) α, rel (fseq n α)
| 0 := λ α a b, true  -- `fseq 0 α` is a singleton type
| (n+1) := r ⟨n+1, nat.pos_of_ne_zero (nat.succ_ne_zero n)⟩

def ext_s₁ {I} (s : I → ℕ₁) (i : I) : ℕ := (s i).1

-- af₁ r I s ↪ af (ext_rel₁ r) I (ext_s₁ s)
def lift_af₁ {r I s α} (x : af₁ r I s α) : af (ext_rel₁ r) I (ext_s₁ s) α :=
⟨x.1, eq.mp begin
  dsimp [ext_s₁],
  induction (s x.1) with n nh,
  induction n,
  { exact false.elim (nat.lt_irrefl 0 nh) },
  { simp [ext_rel₁] }
end x.2⟩

def shape₁ (c : ℕ₁ → ℕ) := Σ n, fin (c n)
def size₁ {c} (x : shape₁ c) := x.1

-- cgf c ↪ af₁ cyclic (shape₁ c) size₁
def lift_cgf {c α} (x : cgf c α) : af₁ cyclic (shape₁ c) size₁ α :=
⟨⟨x.1, x.2.1⟩, x.2.2⟩

-- dgf c k ↪ af₁ (kcyclic k) (shape₁ c) size₁
def lift_dgf {c k α} (x : dgf c k α) : af₁ (kcyclic k) (shape₁ c) size₁ α :=
⟨⟨x.1, x.2.1⟩, x.2.2⟩

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

attribute [simp] function.comp

namespace function
@[simp]
def sum {α β γ δ} (f : α → β) (g : γ → δ) (x : α ⊕ γ) : β ⊕ δ :=
sum.rec (sum.inl ∘ f) (sum.inr ∘ g) x

@[simp]
def prod {α β γ δ} (f : α → β) (g : γ → δ) (x : α × γ) : β × δ :=
(f x.1, g x.2)

@[simp]
def dimap {α β γ δ} (f : α → β) (g : γ → δ) (x : β → γ) : α → δ :=
g ∘ x ∘ f
end function

structure {u v} iso (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x) (fg : Π x, f (g x) = x)

namespace iso
def id {α} : iso α α :=
⟨id, id, by simp [id], by simp [id]⟩

def inv {α β} (i : iso α β) : iso β α :=
⟨i.g, i.f, i.fg, i.gf⟩

def comp {α β γ} (i : iso α β) (j : iso β γ) : iso α γ :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩

def {u} curry {α β γ : Type u} : iso (α → β → γ) ((α × β) → γ) :=
⟨λ f x, f x.1 x.2, λ f x y, f (x, y), by simp, by simp⟩

def sum {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α ⊕ γ) (β ⊕ δ) :=
⟨function.sum i.f j.f,
 function.sum i.g j.g,
 λ x, sum.rec (by simp [i.gf]) (by simp [j.gf]) x,
 λ x, sum.rec (by simp [i.fg]) (by simp [j.fg]) x⟩

def prod {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α × γ) (β × δ) :=
⟨function.prod i.f j.f,
 function.prod i.g j.g,
 by simp [i.gf, j.gf],
 by simp [i.fg, j.fg]⟩

def dimap {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (β → γ) (α → δ) :=
⟨function.dimap i.f j.f,
 function.dimap i.g j.g,
 λ x, funext (by simp [i.fg, j.gf]),
 λ x, funext (by simp [i.gf, j.fg])⟩

def func {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α → γ) (β → δ) :=
dimap i.inv j

def mul_func {α β γ : Type} : iso ((α → γ) × (β → γ)) ((α ⊕ β) → γ) :=
⟨λ x y, sum.rec x.1 x.2 y,
 λ x, (x ∘ sum.inl, x ∘ sum.inr),
 λ x, by simp,
 λ x, by funext y; induction y; repeat { simp }⟩

def sigma_sub {α} {β γ : α → Type} (i : Π a:α, iso (β a) (γ a)) : iso (Σ a:α, β a) (Σ a:α, γ a) :=
⟨λ x, ⟨x.1, (i x.1).f x.2⟩,
 λ x, ⟨x.1, (i x.1).g x.2⟩,
 λ x, by simp [(i x.1).gf],
 λ x, by simp [(i x.1).fg]⟩

def sigma_sum {α} {β γ : α → Type} : iso ((Σ a : α, β a) ⊕ (Σ a : α, γ a)) (Σ a : α, β a ⊕ γ a) :=
⟨λ x, sum.rec (λ y, ⟨y.1, sum.inl y.2⟩) (λ y, ⟨y.1, sum.inr y.2⟩) x,
 λ x, sum.rec (λ y, sum.inl ⟨x.1, y⟩) (λ y, sum.inr ⟨x.1, y⟩) x.2,
 λ x, by induction x; repeat { dsimp, rw sigma.mk.eta },
 λ x, by induction x with x1 x2; induction x2; repeat { refl }⟩

def distr_right {α β γ} : iso ((α ⊕ β) × γ) (α × γ ⊕ β × γ) :=
⟨λ x, sum.rec (λ y, sum.inl (y, x.2)) (λ y, sum.inr (y, x.2)) x.1,
 λ x, sum.rec (λ y, (sum.inl y.1, y.2)) (λ y, (sum.inr y.1, y.2)) x,
 λ x, by induction x with x1 x2; induction x1; repeat { simp },
 λ x, by induction x; repeat { simp }⟩
end iso

namespace fin
@[simp]
def mk.eta {n} (i : fin n) {h} : fin.mk i.val h = i :=
by induction i; simp

def foo {a b x : ℕ} (h : x < a) : x < a + b :=
begin
  induction b,
  { exact h },
  { apply nat.lt_trans b_ih,
    apply nat.lt_succ_of_le,
    exact nat.less_than_or_equal.refl (a + b_n) }
end

def bar {a b x : ℕ} (g : x < a + b) (h : ¬x < a) : x - a < b :=
begin
  have i := nat.eq_or_lt_of_not_lt h,
  induction i,
  { rw i,
    rw i at g,
    rw nat.sub_self,
    have j : a + 0 < a + b := by simp; exact g,
    exact nat.lt_of_add_lt_add_left j },
  { have j : a + (x - a) < a + b :=
    begin
      rw ←nat.add_sub_assoc (nat.le_of_lt i),
      rw nat.add_comm,
      rw nat.add_sub_cancel,
      exact g
    end,
    exact nat.lt_of_add_lt_add_left j }
end

def sum {a b} : iso (fin a ⊕ fin b) (fin (a + b)) :=
⟨λ x, sum.rec (λ y, ⟨y.1, foo y.2⟩) (λ y, ⟨a + y.1, nat.add_lt_add_left y.2 a⟩) x,
 λ x, dite (x.1 < a) (λ h, sum.inl ⟨x.1, h⟩) (λ h, sum.inr ⟨x.1 - a, bar x.2 h⟩),
 begin
   intros,
   induction x,
   { induction x with x xh, exact dif_pos xh },
   { induction x with x xh,
     have h : ¬ a + x < a :=
     begin
       intros h,
       induction x with x xih,
       { exact nat.lt_irrefl a h },
       { have g : a < a + (nat.succ x) := nat.lt_add_of_pos_right (nat.pos_of_ne_zero (nat.succ_ne_zero x)),
         exact nat.nat.lt_asymm h g }
     end,
     simp [dif_neg h, nat.add_sub_cancel_left a x] }
 end,
 begin
   intros,
   induction x with x xh,
   by_cases x < a,
   { rw dif_pos h },
   { rw dif_neg h,
     have i := nat.eq_or_lt_of_not_lt h,
     induction i,
     { simp [i, nat.sub_self a] },
     { simp [nat.add_sub_of_le (nat.le_of_lt i)] }}
 end⟩
end fin

namespace fseq
def mul (n₁ n₂ α) : iso (fseq n₁ α × fseq n₂ α) (fseq (n₁ + n₂) α) :=
iso.mul_func.comp (iso.func fin.sum iso.id)
end fseq

namespace af
def sadd {I₁ I₂} (s₁ : I₁ → ℕ) (s₂ : I₂ → ℕ) : I₁ ⊕ I₂ → ℕ :=
iso.mul_func.f (s₁, s₂)

def smul {I₁ I₂} (s₁ : I₁ → ℕ) (s₂ : I₂ → ℕ) (x : I₁ × I₂) : ℕ :=
s₁ x.1 + s₂ x.2

def add {r I₁ I₂ s₁ s₂ α} : iso ((af r I₁ s₁ α) ⊕ (af r I₂ s₂ α)) (af r (I₁ ⊕ I₂) (sadd s₁ s₂) α) :=
⟨λ x, sum.rec (λ y, ⟨sum.inl y.1, y.2⟩) (λ y, ⟨sum.inr y.1, y.2⟩) x,
 λ x,
 begin
   induction x with x1 x2,
   induction x1,
   { dsimp [sadd] at x2,
     exact sum.inl ⟨x1, x2⟩ },
   { dsimp [sadd] at x2,
     exact sum.inr ⟨x1, x2⟩ }
 end,
 λ x, by induction x; repeat { simp [prod.mk.eta] },
 λ x, by induction x with x1 x2; induction x1; repeat { refl }⟩

def foo {β : ℕ → Type → Type} (r : Π n α, rel (β n α)) {α n m} (f : β n α → β m α → β (n+m) α) : quot (r n α) → quot (r m α) → quot (r (n+m) α) :=
sorry
-- x12 : quot (r (s₁ x11) α),
-- x21 : I₂,
-- x22 : quot (r (s₂ x21) α)
-- ⊢ quot (r (s₁ x11 + s₂ x21) α)
-- analytic_functor.lean:246:2: information trace output
-- fseq (s₁ x11) α → fseq (s₂ x21) α → fseq (s₁ x11 + s₂ x21) α

def mul {r I₁ I₂ s₁ s₂ α} : iso ((af r I₁ s₁ α) × (af r I₂ s₂ α)) (af r (I₁ × I₂) (smul s₁ s₂) α) :=
⟨λ x, begin
  induction x with x1 x2,
  induction x1 with x11 x12,
  induction x2 with x21 x22,
  apply sigma.mk (x11, x21),
  dsimp [smul],
  -- type_check λ x y, (fseq.mul (s₁ x11) (s₂ x21) α).f (x, y),
  type_check foo r,
  -- apply foo r,
  -- type_check
  repeat {sorry},
 end,
 λ x, begin
   induction x with x1 x2,
   dsimp [smul] at x2,
   apply prod.mk,
   { apply sigma.mk x1.1,
     sorry
   },
   { apply sigma.mk x1.2,
     sorry }
 end,
 λ x, sorry,
 λ x, sorry⟩
end af

namespace ogf
@[simp]
def cadd (a b : ℕ → ℕ) (n : ℕ) := a n + b n

@[simp]
def delta (k n : ℕ) := if n = k then 1 else 0

@[simp]
def K (k n : ℕ) := k

def lt_one {n : ℕ} (g : n < 1) : n = 0 :=
begin
  induction n with n ih,
  { refl },
  { exact false.elim (nat.not_lt_zero n (nat.lt_of_succ_lt_succ g)) },
end

def sum_iso (a b : ℕ → ℕ) {α} : iso (ogf a α ⊕ ogf b α) (ogf (cadd a b) α) :=
iso.sigma_sum.comp (iso.sigma_sub (λ n, iso.distr_right.inv.comp (fin.sum.prod iso.id)))

def fseq_iso (k:ℕ) {α} : iso (fseq k α) (ogf (delta k) α) :=
⟨λ x, ⟨k, (⟨0, by simp [nat.zero_lt_succ]⟩, λ i, x i)⟩,
 λ x, dite (x.1=k) (λ h, begin
  induction x with x1 x2,
  induction x2 with x2 x3,
  simp at h,
  simp [h] at x3,
  exact x3
end) (λ h, begin
  induction x with x1 x2,
  induction x2 with x2 x3,
  simp at h,
  simp [h] at x2,
  exact fin.elim0 x2
end),
 λ x, by simp; refl,
 λ x,
 begin
  induction x with x1 x2,
  induction x2 with x2 x3,
  simp,
  by_cases x1 = k,
  { dsimp [h, delta] at *,
    simp [dif_pos h] at *,
    simp [if_pos h] at x2,
    by_cases x2.1 = 0,
    { rename h g,
      congr,
      repeat { rw h },
      { sorry },
      { sorry }},
    { exact false.elim (h (lt_one x2.2)) }},
  { simp [h] at x2,
    exact fin.elim0 x2 }
 end⟩

def fseq_unit_iso {α} : iso unit (fseq 0 α) :=
⟨λ x, fin.elim0,
 λ x, (),
 λ x, by induction x; refl,
 λ x, by funext y; exact fin.elim0 y⟩

def fseq_id_iso {α} : iso α (fseq 1 α) :=
⟨λ x _, x,
 λ x, x 0,
 λ x, rfl,
 λ x,
 begin
  funext y,
  induction y with y yh,
  induction y with y ih,
  { refl },
  { exact false.elim (nat.not_lt_zero y (nat.lt_of_succ_lt_succ yh)) }
 end⟩

def empty_iso {α} : iso empty (ogf (K 0) α) :=
⟨λ x, empty.rec _ x, λ x, fin.elim0 x.2.1,
 λ x, empty.rec _ x, λ x, fin.elim0 x.2.1⟩

def unit_iso {α} : iso unit (ogf (delta 0) α) :=
fseq_unit_iso.comp (fseq_iso 0)

def id_iso {α} : iso α (ogf (delta 1) α) :=
fseq_id_iso.comp (fseq_iso 1)
end ogf

def kem (α) := Σ β, iso α β

def icyc := Σ' p : ℕ → ℕ, ∀ i, p i = p 0 + i
def icyclic (α) (a b : iseq α) := ∃ p : icyc, (a ∘ p.1) = b
def isec (α) := quot (icyclic α)
-- igf x = Σ n : ℕ, cₙ x^ℕ / ℕ
def igf (c : ℕ → ℕ) (α) :=
Σ n : ℕ, fin (c n) × isec α
