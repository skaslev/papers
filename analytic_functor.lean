def ℕ₁ := Σ' n:ℕ, n > 0

def iter {α} (g : α → α) : ℕ → α → α
| 0 := id
| (n+1) := iter n ∘ g

structure {u v} iso (α : Type u) (β : Type v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x) (fg : Π x, f (g x) = x)

def isomorphic (α β) := ∃ i : iso α β, true
def skeleton := quot isomorphic

def perm (n) := Σ' p : fin n → fin n, function.bijective p
def inorb {n} (p : perm n) (a b : fin n) := ∃ s, iter p.1 s a = b
def factor {n} (p : perm n) := quot (inorb p)
def cyc (n : ℕ₁) := Σ' p : perm n.1, ∀ i, p.1 i = p.1 ⟨0, n.2⟩ + i
def kcycles (k n) := Σ' p : perm n, iso (factor p) (fin k)

-- fseq n x = xⁿ
def fseq (n : ℕ) (α : Type) := fin n → α

def ordered (n α) (a b : fseq n α) := a = b
def unordered (n α) (a b : fseq n α) := ∃ p : perm n, (a ∘ p.1) = b
def cyclic (n : ℕ₁) (α) (a b : fseq n.1 α) := ∃ p : cyc n, (a ∘ p.1.1) = b
def kcyclic (k n : ℕ₁) (α) (a b : fseq n.1 α) := ∃ p : kcycles k.1 n.1, (a ∘ p.1.1) = b

-- fset n x = xⁿ / n!
def fset (n α) := quot (unordered n α)

-- fsec n x = xⁿ / n
def fsec (n α) := quot (cyclic n α)

-- ogf c x = Σ n:ℕ, cₙ xⁿ
def ogf (c : ℕ → ℕ) (α) :=
Σ n : ℕ, fin (c n) × fseq n α

-- egf c x = Σ n:ℕ, cₙ xⁿ / n!
def egf (c : ℕ → ℕ) (α) :=
Σ n : ℕ, fin (c n) × fset n α

-- lgf c x = Σ n:ℕ₁, cₙ xⁿ / n
def lgf (c : ℕ₁ → ℕ) (α) :=
Σ n : ℕ₁, fin (c n) × fsec n α

def rel (α) := α → α → Prop

-- Analytic functor
-- This is definition 1.2 from [1] but the relation r doesn't depend
-- on the index i, only on its size s(i)
-- [1] https://www.ms.u-tokyo.ac.jp/~ryu/papers/taa.ps
-- af r s x = Σ i:I, x^s(i) / r(s(i))
def af (r : Π n α, rel (fseq n α)) (I) (s : I → ℕ) (α) :=
Σ i : I, quot (r (s i) α)

def shape {N} (c : N → ℕ) := Σ n, fin (c n)
def size {N c} (x : @shape N c) := x.1

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

def ext_rel₁ (r : Π (n:ℕ₁) α, rel (fseq n.1 α)) : Π n α, rel (fseq n α)
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

-- lgf c ↪ af₁ cyclic (shape c) size
def lift_lgf {c α} (x : lgf c α) : af₁ cyclic (shape c) size α :=
⟨⟨x.1, x.2.1⟩, x.2.2⟩

@[simp] lemma sigma.mk.eta {α} {β : α → Type} : Π {p : Σ α, β α}, sigma.mk p.1 p.2 = p
| ⟨a, b⟩ := rfl

def {u} id_def {α : Sort u} : id = λ x:α, x :=
funext (λ _, rfl)

def isprop (α : Type) := ∀ x y : α, x = y

def isprop_unit : isprop unit
| () () := rfl

attribute [simp] function.comp

namespace function
def add {α β γ δ} (f : α → β) (g : γ → δ) (x : α ⊕ γ) : β ⊕ δ :=
sum.rec (sum.inl ∘ f) (sum.inr ∘ g) x

def mul {α β γ δ} (f : α → β) (g : γ → δ) (x : α × γ) : β × δ :=
(f x.1, g x.2)

def dimap {α β γ δ} (f : α → β) (g : γ → δ) (x : β → γ) : α → δ :=
g ∘ x ∘ f
end function

namespace iso
def id_iso {α} : iso α α :=
⟨id, id, by simp [id], by simp [id]⟩

def inv {α β} (i : iso α β) : iso β α :=
⟨i.g, i.f, i.fg, i.gf⟩

def comp {α β γ} (i : iso α β) (j : iso β γ) : iso α γ :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩

notation a ⁻¹  := inv a
notation a ` ⋆ ` b := comp a b

def {u} curry {α β γ : Type u} : iso (α → β → γ) ((α × β) → γ) :=
⟨λ f x, f x.1 x.2, λ f x y, f (x, y), by simp, by simp⟩

def map {f} [functor f] [is_lawful_functor f] {α β} (i : iso α β) : iso (f α) (f β) :=
⟨functor.map i.f,
 functor.map i.g,
 λ x, by rw ←is_lawful_functor.comp_map; simp [i.gf]; rw [←id_def, is_lawful_functor.id_map],
 λ x, by rw ←is_lawful_functor.comp_map; simp [i.fg]; rw [←id_def, is_lawful_functor.id_map]⟩

def add {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α ⊕ γ) (β ⊕ δ) :=
⟨function.add i.f j.f,
 function.add i.g j.g,
 λ x, sum.rec (by simp [function.add, i.gf]) (by simp [function.add, j.gf]) x,
 λ x, sum.rec (by simp [function.add, i.fg]) (by simp [function.add, j.fg]) x⟩

def mul {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α × γ) (β × δ) :=
⟨function.mul i.f j.f,
 function.mul i.g j.g,
 by simp [function.mul, i.gf, j.gf],
 by simp [function.mul, i.fg, j.fg]⟩

def dimap {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (β → γ) (α → δ) :=
⟨function.dimap i.f j.f,
 function.dimap i.g j.g,
 λ x, funext (by simp [function.dimap, i.fg, j.gf]),
 λ x, funext (by simp [function.dimap, i.gf, j.fg])⟩

def add_left {α β γ} (i : iso α β) : iso (α ⊕ γ) (β ⊕ γ) :=
add i id_iso

def add_right {α γ δ} (i : iso γ δ) : iso (α ⊕ γ) (α ⊕ δ) :=
add id_iso i

def mul_left {α β γ} (i : iso α β) : iso (α × γ) (β × γ) :=
mul i id_iso

def mul_right {α γ δ} (i : iso γ δ) : iso (α × γ) (α × δ) :=
mul id_iso i

def func {α β γ δ} (i : iso α β) (j : iso γ δ) : iso (α → γ) (β → δ) :=
dimap i⁻¹ j

def mul_func {α β γ : Type} : iso ((α → γ) × (β → γ)) ((α ⊕ β) → γ) :=
⟨λ x y, sum.rec x.1 x.2 y,
 λ x, (x ∘ sum.inl, x ∘ sum.inr),
 λ x, by simp,
 λ x, by funext y; induction y; repeat { simp }⟩

def mul_func₂ {α β γ : Type} : iso ((α → β) × (α → γ)) (α → β × γ) :=
⟨λ x y, (x.1 y, x.2 y),
 λ x, (λ y, (x y).1, λ y, (x y).2),
 λ x, by induction x with x₁ x₂; congr,
 λ x, funext (λ y, by simp)⟩

def sigma_subst {α} {β γ : α → Type} (i : Π a:α, iso (β a) (γ a)) : iso (Σ a:α, β a) (Σ a:α, γ a) :=
⟨λ x, ⟨x.1, (i x.1).f x.2⟩,
 λ x, ⟨x.1, (i x.1).g x.2⟩,
 λ x, by simp [(i x.1).gf],
 λ x, by simp [(i x.1).fg]⟩

def sigma_add {α} {β γ : α → Type} : iso ((Σ a : α, β a) ⊕ (Σ a : α, γ a)) (Σ a : α, β a ⊕ γ a) :=
⟨λ x, sum.rec (λ y, ⟨y.1, sum.inl y.2⟩) (λ y, ⟨y.1, sum.inr y.2⟩) x,
 λ x, sum.rec (λ y, sum.inl ⟨x.1, y⟩) (λ y, sum.inr ⟨x.1, y⟩) x.2,
 λ x, by induction x; repeat { dsimp, rw sigma.mk.eta },
 λ x, by induction x with x₁ x₂; induction x₂; repeat { refl }⟩

def sigma_lin {α β} {γ : β → Type} : iso (α × Σ b : β, γ b) (Σ b : β, α × γ b) :=
⟨λ x, ⟨x.2.1, (x.1, x.2.2)⟩,
 λ x, (x.2.1, ⟨x.1, x.2.2⟩),
 λ x, by simp,
 λ x, by induction x with x₁ x₂; simp⟩

def sigma_swap {γ : ℕ → ℕ → Type}: iso (Σ n k, γ n k) (Σ k n, γ n k) :=
⟨λ x, ⟨x.2.1, ⟨x.1, x.2.2⟩⟩,
 λ x, ⟨x.2.1, ⟨x.1, x.2.2⟩⟩,
 λ x, by simp,
 λ x, by simp⟩

def sigma_empty {α} : iso (Σ a : α, empty) empty :=
⟨λ x, x.2, λ x, empty.rec _ x,
 λ x, empty.rec _ x.2, λ x, empty.rec _ x⟩

def sigma_unit {α} : iso (Σ a:α, unit) α :=
⟨λ x, x.1,
 λ x, ⟨x, ()⟩,
 λ x, by induction x with x₁ x₂; induction x₂; refl,
 λ x, by simp⟩

def distr_right {α β γ} : iso ((α ⊕ β) × γ) (α × γ ⊕ β × γ) :=
⟨λ x, sum.rec (λ y, sum.inl (y, x.2)) (λ y, sum.inr (y, x.2)) x.1,
 λ x, sum.rec (λ y, (sum.inl y.1, y.2)) (λ y, (sum.inr y.1, y.2)) x,
 λ x, by induction x with x₁ x₂; induction x₁; repeat { simp },
 λ x, by induction x; repeat { simp }⟩

def add_comm {α β} : iso (α ⊕ β) (β ⊕ α) :=
⟨λ x, sum.rec sum.inr sum.inl x,
 λ x, sum.rec sum.inr sum.inl x,
 λ x, by induction x; simp,
 λ x, by induction x; simp⟩

def mul_comm {α β} : iso (α × β) (β × α) :=
⟨λ x, (x.2, x.1), λ x, (x.2, x.1), by simp, by simp⟩

def mul_assoc {α β γ} : iso (α × (β × γ)) ((α × β) × γ) :=
⟨λ x, ((x.1, x.2.1), x.2.2),
 λ x, (x.1.1, (x.1.2, x.2)),
 λ x, by simp,
 λ x, by simp⟩

def empty_add {α} : iso α (α ⊕ empty) :=
⟨sum.inl, λ x, sum.rec id (empty.rec _) x,
 λ x, rfl, λ x, sum.rec (λ y, rfl) (empty.rec _) x⟩

def empty_mul {α} : iso empty (empty × α) :=
⟨λ x, empty.rec _ x, λ x, empty.rec _ x.1,
 λ x, empty.rec _ x, λ x, empty.rec _ x.1⟩

def unit_mul {α} : iso α (unit × α) :=
⟨λ x, ((), x),
 λ x, x.2,
 λ x, by simp,
 λ x, by induction x with x₁ x₂; congr⟩

def linear {α β γ : Type} (i : iso γ (α ⊕ β × γ)) : iso γ (α × list β) :=
⟨λ x, sum.rec (λ y, (y, [])) (λ y, (sorry, y.1 :: sorry)) (i.f x),
 λ x, list.rec (i.g (sum.inl x.1)) (λ y ys ih, i.g (sum.inr (y, ih))) x.2,
 λ x, sorry,
 λ x, sorry⟩
end iso

def lt_one {n : ℕ} (g : n < 1) : n = 0 :=
begin
  induction n with n ih,
  { refl },
  { exact false.elim (nat.not_lt_zero n (nat.lt_of_succ_lt_succ g)) },
end

namespace fin
@[simp]
def mk.eta {n} (i : fin n) {h} : fin.mk i.val h = i :=
by induction i; simp

def empty_iso : iso empty (fin 0) :=
⟨λ x, empty.rec _ x, λ x, fin.elim0 x,
 λ x, empty.rec _ x, λ x, fin.elim0 x⟩

def unit_iso : iso unit (fin 1) :=
⟨λ x, 0,
 λ x, (),
 λ x, by induction x; refl,
 λ x, by induction x with x h; simp [lt_one h]; congr⟩

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

def add_iso {a b} : iso (fin a ⊕ fin b) (fin (a + b)) :=
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

def pow_iso {n k} : iso (fin k → fin n) (fin (n^k)) :=
sorry
end fin

namespace fseq
def mul_iso (n₁ n₂ α) : iso (fseq n₁ α × fseq n₂ α) (fseq (n₁ + n₂) α) :=
iso.mul_func ⋆ iso.func fin.add_iso iso.id_iso

def unit_iso {α} : iso unit (fseq 0 α) :=
⟨λ x, fin.elim0,
 λ x, (),
 λ x, by induction x; refl,
 λ x, by funext y; exact fin.elim0 y⟩

def unit_iso₂ {n} : iso (fseq n unit) unit :=
⟨λ x, (),
 λ x n, (),
 λ x, by funext; apply isprop_unit,
 λ x, by apply isprop_unit⟩

def id_iso {α} : iso α (fseq 1 α) :=
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

def cons_iso {n α} : iso (α × fseq n α) (fseq (n+1) α) :=
(iso.mul_left id_iso ⋆ iso.mul_comm) ⋆ mul_iso n 1 α
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
   induction x with x₁ x₂,
   induction x₁,
   { dsimp [sadd] at x₂,
     exact sum.inl ⟨x₁, x₂⟩ },
   { dsimp [sadd] at x₂,
     exact sum.inr ⟨x₁, x₂⟩ }
 end,
 λ x, by induction x; repeat { simp [prod.mk.eta] },
 λ x, by induction x with x₁ x₂; induction x₁; repeat { refl }⟩

def foo {β : ℕ → Type → Type} (r : Π n α, rel (β n α)) {α n m} (f : β n α → β m α → β (n+m) α) : quot (r n α) → quot (r m α) → quot (r (n+m) α) :=
sorry
-- x₁₂ : quot (r (s₁ x₁₁) α),
-- x₂₁ : I₂,
-- x₂₂ : quot (r (s₂ x₂₁) α)
-- ⊢ quot (r (s₁ x₁₁ + s₂ x₂₁) α)
-- analytic_functor.lean:246:2: information trace output
-- fseq (s₁ x₁₁) α → fseq (s₂ x₂₁) α → fseq (s₁ x₁₁ + s₂ x₂₁) α

def mul {r I₁ I₂ s₁ s₂ α} : iso ((af r I₁ s₁ α) × (af r I₂ s₂ α)) (af r (I₁ × I₂) (smul s₁ s₂) α) :=
⟨λ x, begin
  induction x with x₁ x₂,
  induction x₁ with x₁₁ x₁₂,
  induction x₂ with x₂₁ x₂₂,
  apply sigma.mk (x₁₁, x₂₁),
  dsimp [smul],
  -- type_check λ x y, (fseq.mul_iso (s₁ x₁₁) (s₂ x₂₁) α).f (x, y),
  type_check foo r,
  -- apply foo r,
  -- type_check
  repeat {sorry},
 end,
 λ x, begin
   induction x with x₁ x₂,
   dsimp [smul] at x₂,
   apply prod.mk,
   { apply sigma.mk x₁.1,
     sorry
   },
   { apply sigma.mk x₁.2,
     sorry }
 end,
 λ x, sorry,
 λ x, sorry⟩
end af

def delta (k n : ℕ) := ite (n = k) 1 0

def K (k n : ℕ) := k

def partial_sum (f : ℕ → ℕ) : ℕ → ℕ
| 0 := f 0
| (n+1) := partial_sum n + f (n+1)

namespace ogf
def cadd (a b : ℕ → ℕ) (n : ℕ) := a n + b n

def cmul (a b : ℕ → ℕ) (n : ℕ) := partial_sum (λ k, a k * b (n - k)) n

def add_iso {a b α} : iso (ogf a α ⊕ ogf b α) (ogf (cadd a b) α) :=
iso.sigma_add ⋆ iso.sigma_subst (λ n, iso.distr_right⁻¹ ⋆ iso.mul_left fin.add_iso)

def mul_iso {a b α} : iso (ogf a α × ogf b α) (ogf (cmul a b) α) := sorry

def fseq_iso (k:ℕ) {α} : iso (fseq k α) (ogf (delta k) α) :=
⟨λ x, ⟨k, (⟨0, by simp [delta, nat.zero_lt_succ]⟩, λ i, x i)⟩,
 λ x, dite (x.1=k) (λ h, begin
  induction x with x₁ x₂,
  induction x₂ with x₂ x₃,
  simp at h,
  simp [h] at x₃,
  exact x₃
end) (λ h, begin
  induction x with x₁ x₂,
  induction x₂ with x₂ x₃,
  simp at h,
  simp [delta, h] at x₂,
  exact fin.elim0 x₂
end),
 λ x, by simp; refl,
 λ x,
 begin
  induction x with x₁ x₂,
  induction x₂ with x₂ x₃,
  simp,
  by_cases x₁ = k,
  { dsimp [h, delta] at *,
    simp [dif_pos h] at *,
    simp [if_pos h] at x₂,
    by_cases x₂.1 = 0,
    { rename h g,
      congr,
      repeat { rw h },
      { sorry },
      { sorry }},
    { exact false.elim (h (lt_one x₂.2)) }},
  { simp [delta, h] at x₂,
    exact fin.elim0 x₂ }
 end⟩

def empty_iso {α} : iso empty (ogf (K 0) α) :=
⟨λ x, empty.rec _ x, λ x, fin.elim0 x.2.1,
 λ x, empty.rec _ x, λ x, fin.elim0 x.2.1⟩

def unit_iso {α} : iso unit (ogf (delta 0) α) :=
fseq.unit_iso ⋆ fseq_iso 0

def id_iso {α} : iso α (ogf (delta 1) α) :=
fseq.id_iso ⋆ fseq_iso 1
end ogf

section generic_summation
def ax₀ {f : ℕ → Type} : iso (Σ n:ℕ, f n) (f 0 ⊕ Σ n:ℕ₁, f n.1) :=
sorry

def ax₁ {f : ℕ → Type} : iso (Σ n:ℕ, f n) (f 0 ⊕ Σ n:ℕ, f (n+1)) :=
⟨λ x, dite (x.1 < 1)
 (λ h, sum.inl (eq.mp (by rw lt_one h) x.2))
 (λ h, sum.inr ⟨x.1 - 1, eq.mp (begin
   congr,
   apply eq.symm,
   apply nat.sub_add_cancel,
   have y := nat.lt_or_ge x.1 1,
   induction y,
   { exact false.elim (h y) },
   exact y
 end) x.2⟩),
 λ x, sum.rec (λ y, ⟨0, y⟩) (λ y, ⟨y.1 + 1, y.2⟩) x,
 λ x, begin
   induction x with x₁ x₂,
   simp,
   by_cases x₁ < 1,
   { rw dif_pos h,
     have y : x₁ = 0 := lt_one h,
     simp [y],
     sorry
   },
   { rw dif_neg h,
     simp,
     sorry }
 end,
 λ x, sorry⟩

def ax₂ {f : ℕ → Type} {α} : iso (Σ n:ℕ, α × f n) (α × Σ n:ℕ, f n) :=
iso.sigma_lin⁻¹
end generic_summation

namespace nat
def ogf_iso : iso ℕ (ogf (K 1) unit) :=
iso.sigma_unit⁻¹ ⋆ iso.sigma_subst (λ n, iso.unit_mul ⋆ (iso.mul fin.unit_iso⁻¹ fseq.unit_iso₂)⁻¹)
end nat

-- Geometric power series
-- geom x = Σ n:ℕ, xⁿ
def geom (α) := Σ n, fseq n α

namespace geom
def lin_iso {α} : iso (geom α) (unit ⊕ α × (geom α)) :=
ax₁ ⋆ iso.add fseq.unit_iso⁻¹ (iso.sigma_subst (λ n, fseq.cons_iso⁻¹) ⋆ iso.sigma_lin⁻¹)

def list_iso {α} : iso (geom α) (list α) :=
iso.linear lin_iso ⋆ iso.unit_mul⁻¹

def ogf_iso {α} : iso (geom α) (ogf (K 1) α) :=
iso.sigma_subst (λ n, iso.unit_mul ⋆ iso.mul_left fin.unit_iso)
end geom

namespace list
def def_iso {α} : iso (list α) (unit ⊕ α × (list α)) :=
⟨λ x, list.rec (sum.inl ()) (λ h t ih, sum.inr (h, t)) x,
 λ x, sum.rec (λ y, []) (λ y, y.1 :: y.2) x,
 λ x, by induction x; repeat { simp },
 λ x, by induction x; { induction x, refl }; { simp }⟩

def ogf_iso {α} : iso (list α) (ogf (K 1) α) :=
geom.list_iso⁻¹ ⋆ geom.ogf_iso

def nat_iso : iso (list unit) ℕ :=
ogf_iso ⋆ nat.ogf_iso⁻¹
end list

namespace fins
-- 0⁰ = 1
def unit_iso : iso (fin 0 → fin 0) unit :=
⟨λ x, (),
 λ x, fin.elim0,
 λ x, funext (λ y, fin.elim0 y),
 λ x, by induction x; refl⟩

-- 0ⁿ⁺¹ = 0
def empty_iso {n} : iso (fin (n + 1) → fin 0) empty :=
⟨λ x, fin.elim0 (x 0),
 λ x, empty.rec _ x,
 λ x, funext (λ y, fin.elim0 (x y)),
 λ x, empty.rec _ x⟩

-- Σ k, nᵏ = list n
def list_iso {n} : iso (Σ k, fin k → fin n) (list (fin n)) :=
geom.list_iso

-- Σ k, nᵏ = ogf (λ k, n^k) 1
def ogf_iso {n} : iso (Σ k, fin k → fin n) (ogf (λ k, n^k) unit) :=
iso.sigma_subst (λ k, iso.unit_mul ⋆ iso.mul_comm⁻¹ ⋆ iso.mul fin.pow_iso fseq.unit_iso₂⁻¹)
end fins

def list_unit_iso : iso (list empty) unit :=
iso.map fin.empty_iso ⋆ geom.list_iso⁻¹ ⋆ ax₁ ⋆
  iso.add fins.unit_iso (iso.sigma_subst (λ n, fins.empty_iso) ⋆ iso.sigma_empty) ⋆ iso.empty_add⁻¹

-- f(x) = x + f(g(x)) ↔ f(x) = Σ n:ℕ, gⁿ(x)
inductive F (g : Type → Type) : Type → Type 1
| F₀ : Π {α}, α → F α
| F₁ : Π {α}, F (g α) → F α

-- s(x) = Σ n:ℕ, gⁿ(x)
def S (g : Type → Type) (α) := Σ n : ℕ, iter g n α

namespace S
def diter {β : Type → Type 1} {γ : Type → Type} (g : Π {α}, β (γ α) → β α) : Π (n : ℕ) {α}, β (iter γ n α) → β α
| 0 α := id
| (n+1) α := g ∘ diter n

def code {g α} (x : S g α) : F g α :=
diter (@F.F₁ g) x.1 (F.F₀ g x.2)

def deco {g α} (x : F g α) : S g α :=
F.rec (λ α a, ⟨0, a⟩) (λ α a ih, ⟨ih.1+1, ih.2⟩) x

def deco_code {g α} (x : S g α) : deco (code x) = x :=
begin
  simp [deco, code],
  induction x with n x,
  induction n with m ih generalizing α,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

def code_deco {g α} (x : F g α) : code (deco x) = x :=
begin
  simp [deco, code],
  induction x with β x β x ih,
  { dsimp [diter], refl },
  { dsimp [diter], rw ih }
end

-- s(x) = f(x)
def f_iso {g : Type → Type} {α} : iso (S g α) (F g α) :=
⟨code, deco, deco_code, code_deco⟩
end S

-- g(x) = x + x g(x) ↔ g(x) = x/(1-x) ↔ gⁿ(x) = x/(1-nx)
inductive G (α : Type) : Type
| G₀ : α → G
| G₁ : α → G → G

namespace G
def def_iso {α} : iso (G α) (α ⊕ α × (G α)) :=
⟨λ x, G.rec sum.inl (λ h t ih, sum.inr (h, t)) x,
 λ x, sum.rec G.G₀ (λ y, G.G₁ y.1 y.2) x,
 λ x, by induction x; repeat { refl },
 λ x, by induction x; repeat { simp }⟩

def list_iso {α} : iso (G α) (α × (list α)) :=
iso.linear def_iso

def cf (n : ℕ) := ite (n = 0) 0 1

def cf_lemma : cf = ogf.cmul (delta 1) (K 1) :=
begin
  funext n,
  by_cases n=0,
  { simp [h, cf, delta, K, ogf.cmul, partial_sum] },
  simp [h, cf, delta, K, ogf.cmul, partial_sum],
  induction n with n ih,
  { exact false.elim (h rfl) },
  simp [partial_sum],
  by_cases n=0,
  { rename h g,
    simp [g, partial_sum] },
  { rename h g,
    rw ←ih g,
    have h₁ : ¬n+1=1 := λ x, false.elim (g (add_right_cancel x)),
    rw if_neg h₁ }
end

def ogf_iso {α} : iso (G α) (ogf cf α) :=
eq.mp (by rw cf_lemma) (list_iso ⋆ iso.mul ogf.id_iso list.ogf_iso ⋆ ogf.mul_iso)
end G

namespace Gⁿ
-- gⁿ(x) = x/(1-nx)
def list_iso {n α} : iso (iter G n α) (α × list (fin n × α)) :=
begin
  induction n with n ih generalizing α,
  { exact (iso.unit_mul ⋆ iso.mul_comm ⋆
      iso.mul_right (list_unit_iso⁻¹ ⋆ iso.map (iso.empty_mul ⋆ iso.mul_left fin.empty_iso))) },
  apply iso.comp ih _,
  apply (iso.mul_right geom.list_iso.inv ⋆ _),
  apply (_ ⋆ iso.mul_right geom.list_iso),
  apply (ax₂.inv ⋆ _),
  apply (_ ⋆ ax₂),
  apply (iso.sigma_subst (λ k, _)),
  apply (iso.mul_right iso.mul_func₂.inv ⋆ _),
  apply (_ ⋆ iso.mul_right iso.mul_func₂),
  apply (iso.mul_comm ⋆ iso.mul_assoc.inv ⋆ _),
  apply (iso.mul_right (iso.mul_comm ⋆ fseq.cons_iso) ⋆ _),
  apply (_ ⋆ iso.mul_assoc ⋆ iso.mul_comm),
  apply (_ ⋆ iso.mul_right (fseq.cons_iso.inv ⋆ iso.mul_comm)),

  apply (iso.mul_left fin.pow_iso ⋆ _),
  apply (_ ⋆ (iso.mul_left fin.pow_iso).inv),

  -- apply (iso.mul_right (iso.func (@fin.add_iso k 1).inv G.def_iso ⋆ iso.mul_func.inv) ⋆ _),
  -- apply (iso_mul_right (iso.mul_right fseq.id_iso.inv) ⋆ _)
  sorry
end

def list_iso₁ {n} : iso (iter G n unit) (list (fin n)) :=
list_iso ⋆ iso.unit_mul⁻¹ ⋆ iso.map (iso.mul_comm ⋆ iso.unit_mul⁻¹)

-- gⁿ(x) = Σ k:ℕ, nᵏ x^(k+1) = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- Thm fins_iso: ∀ n:ℕ, gⁿ(unit) = Σ k:ℕ, fin k → fin n
-- => f(unit) = Σ n:ℕ, gⁿ(unit) = Σ n:ℕ, Σ k:ℕ, fin k → fin n
def fins_iso {n} : iso (iter G n unit) (Σ k, fin k → fin n) :=
list_iso₁ ⋆ fins.list_iso⁻¹

def cf (n k : ℕ) : ℕ := dite (k = 0) (λ _, 0) (λ _, n^(k-1))

def cf_lemma₁ (n : ℕ) : cf n 0 = 0 :=
by simp [cf]

def cf_lemma₂ (n k : ℕ) : cf n (k+1) = n^k :=
by simp [cf, dif_neg (nat.succ_ne_zero k)]

def ogf_iso {n α} : iso (iter G n α) (ogf (cf n) α) :=
begin
  apply (list_iso ⋆ iso.mul_right geom.list_iso⁻¹ ⋆ _),
  apply (_ ⋆ ax₁.inv),
  rw cf_lemma₁,
  apply (_ ⋆ iso.empty_add ⋆ iso.add_comm ⋆ iso.add_left (iso.empty_mul ⋆ iso.mul_left fin.empty_iso)),
  apply (ax₂.inv ⋆ _),
  apply iso.sigma_subst (λ k, _),
  apply (_ ⋆ iso.mul_assoc ⋆ iso.mul_comm ⋆ iso.mul_right fseq.cons_iso),
  apply iso.mul_right,
  apply (_ ⋆ iso.mul_comm),
  apply (iso.mul_func₂.inv ⋆ _),
  apply iso.mul_left,
  apply (fin.pow_iso ⋆ _),
  rw cf_lemma₂,
  apply iso.id_iso
end
end Gⁿ

namespace S
def fins_iso : iso (S G unit) (Σ n k, fin k → fin n) :=
iso.sigma_subst (λ n, Gⁿ.fins_iso)

def list_iso {α} : iso (S G α) (Σ n, α × list (fin n × α)) :=
iso.sigma_subst (λ n, Gⁿ.list_iso)

def list_iso₁ : iso (S G unit) (Σ n, list (fin n)) :=
fins_iso ⋆ iso.sigma_subst (λ n, fins.list_iso)
end S

namespace F
def fins_iso : iso (F G unit) (Σ n k, fin k → fin n) :=
S.f_iso⁻¹ ⋆ S.fins_iso

def list_iso {α} : iso (F G α) (Σ n, α × list (fin n × α)) :=
S.f_iso⁻¹ ⋆ S.list_iso

def list_iso₁ : iso (F G unit) (Σ n, list (fin n)) :=
S.f_iso⁻¹ ⋆ S.list_iso₁
end F

-- From Generatingfunctionology pg. 18
-- B₀(x) = 1, ∀ k>0:
-- Bₖ(x) = x Bₖ₋₁(x) + k x Bₖ(x)
-- ⇒ Bₖ x = x/(1-kx) Bₖ₋₁(x)
inductive B (α : Type) : ℕ → Type
| B₀ : B 0
| B₁ {k} : α → (B k) → B (k+1)
| B₂ {k} : α → fin (k+1) → B (k+1) → B (k+1)

def ogf_skel (f : ℕ → ℕ) (α) := Σ β : Type → Type, iso (β α) (ogf f α)
def ogf_fixed (f : ℕ → ℕ) := Σ α, iso α (ogf f α)

def icyc := Σ' p : ℕ → ℕ, ∀ i, p i = p 0 + i
def icyclic (α) (a b : iseq α) := ∃ p : icyc, (a ∘ p.1) = b
def isec (α) := quot (icyclic α)
-- igf x = Σ n : ℕ, cₙ x^ℕ / ℕ
def igf (c : ℕ → ℕ) (α) :=
Σ n : ℕ, fin (c n) × isec α
