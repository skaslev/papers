-- Analytic combinatorics[1,2] is a wonderful subject for analyzing large
-- combinatorial structures using methods from complex analysis.
-- This is an attempt to formalize some of the ideas in Lean.
-- [1] https://aofa.cs.princeton.edu/home
-- [2] http://algo.inria.fr/flajolet/Publications/book.pdf

def ℕ₁ := Σ' n:ℕ, n > 0

def iter {α} (g : α → α) : ℕ → α → α
| 0 := id
| (n+1) := iter n ∘ g

structure {u v} iso (α : Sort u) (β : Sort v) :=
(f : α → β) (g : β → α) (gf : Π x, g (f x) = x) (fg : Π x, f (g x) = x)

notation a ` ≃ ` b := iso a b

def isomorphic (α β) := ∃ i : α ≃ β, true
def skeleton := quot isomorphic

def perm (n) := fin n ≃ fin n
def orbit {n} (p : perm n) (a b : fin n) := ∃ k, iter p.1 k a = b
def factor {n} (p : perm n) := quot (orbit p)
def kcycles (k n) := Σ p : perm n, factor p ≃ fin k
def cyc (n : ℕ₁) := Σ' p : perm n.1, ∀ i, p.1 i = p.1 ⟨0, n.2⟩ + i

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
-- This is definition 1.2 from [3] but the relation r doesn't depend
-- on the index i, only on its size s(i)
-- [3] https://www.ms.u-tokyo.ac.jp/~ryu/papers/taa.ps
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
def id_iso {α} : α ≃ α :=
⟨id, id, by simp [id], by simp [id]⟩

def inv {α β} (i : α ≃ β) : β ≃ α :=
⟨i.g, i.f, i.fg, i.gf⟩

def comp {α β γ} (i : α ≃ β) (j : β ≃ γ) : α ≃ γ :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩

notation a ⁻¹  := inv a
notation a ` ⋆ ` b := comp a b

def map {f} [functor f] [is_lawful_functor f] {α β} (i : α ≃ β) : f α ≃ f β :=
⟨functor.map i.f,
 functor.map i.g,
 λ x, by rw ←is_lawful_functor.comp_map; simp [i.gf]; rw [←id_def, is_lawful_functor.id_map],
 λ x, by rw ←is_lawful_functor.comp_map; simp [i.fg]; rw [←id_def, is_lawful_functor.id_map]⟩

def add {α β γ δ} (i : α ≃ β) (j : γ ≃ δ) : α ⊕ γ ≃ β ⊕ δ :=
⟨function.add i.f j.f,
 function.add i.g j.g,
 λ x, sum.rec (by simp [function.add, i.gf]) (by simp [function.add, j.gf]) x,
 λ x, sum.rec (by simp [function.add, i.fg]) (by simp [function.add, j.fg]) x⟩

def mul {α β γ δ} (i : α ≃ β) (j : γ ≃ δ) : α × γ ≃ β × δ :=
⟨function.mul i.f j.f,
 function.mul i.g j.g,
 by simp [function.mul, i.gf, j.gf],
 by simp [function.mul, i.fg, j.fg]⟩

def dimap {α β γ δ} (i : α ≃ β) (j : γ ≃ δ) : β → γ ≃ α → δ :=
⟨function.dimap i.f j.f,
 function.dimap i.g j.g,
 λ x, funext (by simp [function.dimap, i.fg, j.gf]),
 λ x, funext (by simp [function.dimap, i.gf, j.fg])⟩

def add_left {α β γ} (i : α ≃ β) : α ⊕ γ ≃ β ⊕ γ :=
add i id_iso

def add_right {α γ δ} (i : γ ≃ δ) : α ⊕ γ ≃ α ⊕ δ :=
add id_iso i

def mul_left {α β γ} (i : α ≃ β) : α × γ ≃ β × γ :=
mul i id_iso

def mul_right {α γ δ} (i : γ ≃ δ) : α × γ ≃ α × δ :=
mul id_iso i

def func {α β γ δ} (i : α ≃ β) (j : γ ≃ δ) : α → γ ≃ β → δ :=
dimap i⁻¹ j

def func_right {α β γ} (i : β ≃ γ) : α → β ≃ α → γ :=
func id_iso i

def func_left {α β γ} (i : α ≃ β) : α → γ ≃ β → γ :=
func i id_iso

-- (cᵇ)ᵃ = cᵃᵇ
def curry {α β γ : Type} : α → β → γ ≃ (α × β) → γ :=
⟨λ f x, f x.1 x.2, λ f x y, f (x, y), by simp, by simp⟩

-- cᵃ cᵇ = cᵃ⁺ᵇ
def mul_func₁ {α β γ : Type} : (α → γ) × (β → γ) ≃ (α ⊕ β) → γ :=
⟨λ x y, sum.rec x.1 x.2 y,
 λ x, (x ∘ sum.inl, x ∘ sum.inr),
 λ x, by simp,
 λ x, by funext y; induction y; repeat { simp }⟩

-- bᵃ cᵃ = (bc)ᵃ
def mul_func₂ {α β γ : Type} : (α → β) × (α → γ) ≃ α → β × γ :=
⟨λ x y, (x.1 y, x.2 y),
 λ x, (λ y, (x y).1, λ y, (x y).2),
 λ x, by induction x with x₁ x₂; congr,
 λ x, funext (λ y, by simp)⟩

def sigma_subst {α} {β γ : α → Type} (i : Π a:α, β a ≃ γ a) : (Σ a:α, β a) ≃ Σ a:α, γ a :=
⟨λ x, ⟨x.1, (i x.1).f x.2⟩,
 λ x, ⟨x.1, (i x.1).g x.2⟩,
 λ x, begin induction x with x₁ x₂, simp [(i x₁).gf], end,
 λ x, begin induction x with x₁ x₂, simp [(i x₁).fg] end⟩

def sigma_add {α} {β γ : α → Type} : ((Σ a : α, β a) ⊕ (Σ a : α, γ a)) ≃ Σ a : α, β a ⊕ γ a :=
⟨λ x, sum.rec (λ y, ⟨y.1, sum.inl y.2⟩) (λ y, ⟨y.1, sum.inr y.2⟩) x,
 λ x, sum.rec (λ y, sum.inl ⟨x.1, y⟩) (λ y, sum.inr ⟨x.1, y⟩) x.2,
 λ x, by induction x; repeat { dsimp, rw sigma.mk.eta },
 λ x, by induction x with x₁ x₂; induction x₂; repeat { refl }⟩

def sigma_distr {α β} {γ : β → Type} : (α × Σ b : β, γ b) ≃ Σ b : β, α × γ b :=
⟨λ x, ⟨x.2.1, (x.1, x.2.2)⟩,
 λ x, (x.2.1, ⟨x.1, x.2.2⟩),
 λ x, by simp,
 λ x, by induction x with x₁ x₂; simp⟩

def sigma_swap {γ : ℕ → ℕ → Type}: (Σ n k, γ n k) ≃ Σ k n, γ n k :=
⟨λ x, ⟨x.2.1, ⟨x.1, x.2.2⟩⟩,
 λ x, ⟨x.2.1, ⟨x.1, x.2.2⟩⟩,
 λ x, by simp,
 λ x, by simp⟩

def sigma_empty {α} : (Σ a : α, empty) ≃ empty :=
⟨λ x, x.2, λ x, empty.rec _ x,
 λ x, empty.rec _ x.2, λ x, empty.rec _ x⟩

def sigma_unit {α} : (Σ a:α, unit) ≃ α :=
⟨λ x, x.1,
 λ x, ⟨x, ()⟩,
 λ x, by induction x with x₁ x₂; induction x₂; refl,
 λ x, by simp⟩

def add_comm {α β} : α ⊕ β ≃ β ⊕ α :=
⟨λ x, sum.rec sum.inr sum.inl x,
 λ x, sum.rec sum.inr sum.inl x,
 λ x, by induction x; simp,
 λ x, by induction x; simp⟩

def mul_comm {α β} : α × β ≃ β × α :=
⟨λ x, (x.2, x.1), λ x, (x.2, x.1), by simp, by simp⟩

def add_assoc {α β γ} : α ⊕ (β ⊕ γ) ≃ (α ⊕ β) ⊕ γ :=
⟨λ x, sum.rec (sum.inl ∘ sum.inl) (λ y, sum.rec (sum.inl ∘ sum.inr) sum.inr y) x,
 λ x, sum.rec (λ y, sum.rec sum.inl (sum.inr ∘ sum.inl) y) (sum.inr ∘ sum.inr) x,
 λ x, by repeat { induction x, repeat { refl } },
 λ x, by repeat { induction x, repeat { refl } }⟩

def mul_assoc {α β γ} : α × (β × γ) ≃ (α × β) × γ :=
⟨λ x, ((x.1, x.2.1), x.2.2),
 λ x, (x.1.1, (x.1.2, x.2)),
 λ x, by simp,
 λ x, by simp⟩

def distr_right {α β γ} : (α ⊕ β) × γ ≃ α × γ ⊕ β × γ :=
⟨λ x, sum.rec (λ y, sum.inl (y, x.2)) (λ y, sum.inr (y, x.2)) x.1,
 λ x, sum.rec (λ y, (sum.inl y.1, y.2)) (λ y, (sum.inr y.1, y.2)) x,
 λ x, by induction x with x₁ x₂; induction x₁; repeat { simp },
 λ x, by induction x; repeat { simp }⟩

def distr_left {α β γ} : α × (β ⊕ γ) ≃ α × β ⊕ α × γ :=
mul_comm ⋆ distr_right ⋆ iso.add mul_comm mul_comm

def empty_add_right {α} : α ≃ α ⊕ empty :=
⟨sum.inl, λ x, sum.rec id (empty.rec _) x,
 λ x, rfl, λ x, sum.rec (λ y, rfl) (empty.rec _) x⟩

def empty_add_left {α} : α ≃ empty ⊕ α :=
empty_add_right ⋆ add_comm

def empty_mul_right {α} : empty ≃ α × empty :=
⟨λ x, empty.rec _ x, λ x, empty.rec _ x.2,
 λ x, empty.rec _ x, λ x, empty.rec _ x.2⟩

def empty_mul_left {α} : empty ≃ empty × α :=
empty_mul_right ⋆ mul_comm

def unit_mul_right {α} : α ≃ α × unit :=
⟨λ x, (x, ()),
 λ x, x.1,
 λ x, by simp,
 λ x, by induction x with x₁ x₂; congr⟩

def unit_mul_left {α} : α ≃ unit × α :=
unit_mul_right ⋆ mul_comm

def distr_unit_left {α β} : α ⊕ α × β ≃ α × (unit ⊕ β) :=
iso.add_left iso.unit_mul_right ⋆ iso.distr_left⁻¹

def distr_unit_right {α β} : α ⊕ β × α ≃ (unit ⊕ β) × α :=
iso.add_right iso.mul_comm ⋆ distr_unit_left ⋆ iso.mul_comm
end iso

def lt_one {n : ℕ} (g : n < 1) : n = 0 :=
begin
  induction n with n ih,
  { refl },
  { exact false.elim (nat.not_lt_zero n (nat.lt_of_succ_lt_succ g)) },
end

section generic_summation
def ax₁ {f : ℕ → Type} : (Σ n:ℕ, f n) ≃ f 0 ⊕ Σ n:ℕ, f (n+1) :=
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
 λ x,
 begin
   induction x with x₁ x₂,
   by_cases x₁ < 1,
   { rw dif_pos h,
     have y : x₁ = 0 := lt_one h,
     simp [y],
     apply eq_rec_heq },
   { rw dif_neg h,
     simp,
     split,
     { rw nat.add_comm,
       rw nat.sub_add_cancel,
       exact le_of_not_gt h },
     { apply eq_rec_heq }}
 end,
 λ x,
 begin
   induction x,
   { dsimp,
     have h : 0 < 1 := nat.lt.base 0,
     rw dif_pos h,
     refl },
   { induction x with n x,
     dsimp,
     have h : ¬ n + 1 < 1 := λ x, nat.not_lt_zero n (nat.lt_of_succ_lt_succ x),
     rw dif_neg h,
     refl }
 end⟩

def ax₂ {f : ℕ → Type} {α} : (Σ n:ℕ, α × f n) ≃ α × Σ n:ℕ, f n :=
iso.sigma_distr⁻¹
end generic_summation

def delta (k n : ℕ) := ite (n = k) 1 0

def K (k n : ℕ) := k

def partial_sum (f : ℕ → ℕ) : ℕ → ℕ
| 0 := f 0
| (n+1) := partial_sum n + f (n+1)

namespace fin
@[simp]
def mk.eta {n} (i : fin n) {h} : fin.mk i.val h = i :=
by induction i; simp

def empty_iso : fin 0 ≃ empty :=
⟨λ x, fin.elim0 x, λ x, empty.rec _ x,
 λ x, fin.elim0 x, λ x, empty.rec _ x⟩

def unit_iso : fin 1 ≃ unit :=
⟨λ x, (),
 λ x, 0,
 λ x, by induction x with x h; simp [lt_one h]; congr,
 λ x, by induction x; refl⟩

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

def add_iso {a b} : fin a ⊕ fin b ≃ fin (a + b) :=
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

def add_unit_iso {n} : unit ⊕ fin n ≃ fin (n+1) :=
iso.add_comm ⋆ iso.add_right fin.unit_iso.inv ⋆ fin.add_iso

def mul_iso {n m} : fin n × fin m ≃ fin (n * m) :=
sorry

def pow_iso {n k} : fin k → fin n ≃ fin (n^k) :=
sorry
end fin

namespace fseq
def unit_iso {α} : fseq 0 α ≃ unit :=
⟨λ x, (),
 λ x, fin.elim0,
 λ x, by funext y; exact fin.elim0 y,
 λ x, by induction x; refl⟩

def unit_iso₂ {n} : fseq n unit ≃ unit :=
⟨λ x, (),
 λ x n, (),
 λ x, by funext; apply isprop_unit,
 λ x, by apply isprop_unit⟩

def id_iso {α} : fseq 1 α ≃ α :=
⟨λ x, x 0,
 λ x _, x,
 λ x,
 begin
  funext y,
  induction y with y yh,
  induction y with y ih,
  { refl },
  { exact false.elim (nat.not_lt_zero y (nat.lt_of_succ_lt_succ yh)) }
 end,
 λ x, rfl⟩

def mul_iso (n₁ n₂ α) : fseq n₁ α × fseq n₂ α ≃ fseq (n₁ + n₂) α :=
iso.mul_func₁ ⋆ iso.func_left fin.add_iso

def cons_iso {n α} : α × fseq n α ≃ fseq (n+1) α :=
iso.mul_left id_iso⁻¹ ⋆ eq.mp (by rw nat.add_comm) (mul_iso 1 n α)

def ogf_iso {k α} : fseq k α ≃ ogf (delta k) α :=
⟨λ x, ⟨k, (⟨0, by simp [delta, nat.zero_lt_succ]⟩, x)⟩,
 λ x, dite (x.1=k) (λ h, eq.mp (by rw h) x.2.2) (λ h, fin.elim0 (eq.mp (by simp [delta, if_neg h]) x.2.1)),
 λ x, by simp; refl,
 λ x,
 begin
  induction x with n x,
  induction x with c x,
  dsimp,
  by_cases n = k,
  { simp [dif_pos h],
    dsimp [delta, if_pos h] at c,
    congr,
    repeat { rw ←h },
    { induction c with c c_h,
      induction c with c ih,
      { sorry },
      { simp [delta, if_pos h] at c_h,
        exact false.elim (nat.not_lt_zero _ (nat.lt_of_succ_lt_succ c_h)) }},
    { apply eq_rec_heq }},
  { simp [delta, h] at c,
    exact fin.elim0 c }
 end⟩
end fseq

namespace af
def sadd {I₁ I₂} (s₁ : I₁ → ℕ) (s₂ : I₂ → ℕ) : I₁ ⊕ I₂ → ℕ :=
iso.mul_func₁.f (s₁, s₂)

def smul {I₁ I₂} (s₁ : I₁ → ℕ) (s₂ : I₂ → ℕ) (x : I₁ × I₂) : ℕ :=
s₁ x.1 + s₂ x.2

def add_iso {r I₁ I₂ s₁ s₂ α} : (af r I₁ s₁ α) ⊕ (af r I₂ s₂ α) ≃ af r (I₁ ⊕ I₂) (sadd s₁ s₂) α :=
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


def mul_iso {r I₁ I₂ s₁ s₂ α} : (af r I₁ s₁ α) × (af r I₂ s₂ α) ≃ af r (I₁ × I₂) (smul s₁ s₂) α :=
sorry
end af

namespace ogf
def cadd (a b : ℕ → ℕ) (n : ℕ) := a n + b n

def cmul (a b : ℕ → ℕ) (n : ℕ) := partial_sum (λ k, a k * b (n - k)) n

def add_iso {a b α} : ogf a α ⊕ ogf b α ≃ ogf (cadd a b) α :=
iso.sigma_add ⋆ iso.sigma_subst (λ n, iso.distr_right⁻¹ ⋆ iso.mul_left fin.add_iso)

-- Σ n, cₙ xⁿ = c₀ + x Σ n, cₙ₊₁ xⁿ
def foo_iso {c : ℕ → ℕ} {α} : (Σ n, fin (c n) × fseq n α) ≃ fin (c 0) ⊕ α × Σ n, fin (c (n+1)) × fseq n α :=
begin
  apply (ax₁ ⋆ _),
  apply (iso.add_left (iso.mul_right fseq.unit_iso ⋆ iso.unit_mul_right.inv) ⋆ _),
  apply iso.add_right,
  apply (_ ⋆ ax₂),
  apply iso.sigma_subst (λ n, _),
  apply (_ ⋆ iso.mul_assoc ⋆ iso.mul_comm),
  apply iso.mul_right,
  apply (_ ⋆ iso.mul_comm),
  apply fseq.cons_iso.inv
end

def mul_iso {a b α} : ogf a α × ogf b α ≃ ogf (cmul a b) α :=
sorry
end ogf

namespace empty
def ogf_iso {α} : empty ≃ ogf (K 0) α :=
⟨λ x, empty.rec _ x, λ x, fin.elim0 x.2.1,
 λ x, empty.rec _ x, λ x, fin.elim0 x.2.1⟩
end empty

namespace unit
def ogf_iso {α} : unit ≃ ogf (delta 0) α :=
fseq.unit_iso⁻¹ ⋆ fseq.ogf_iso
end unit

namespace id
def ogf_iso {α} : α ≃ ogf (delta 1) α :=
fseq.id_iso⁻¹ ⋆ fseq.ogf_iso
end id

namespace option
-- option x = 1 + x
def def_iso {α} : option α ≃ unit ⊕ α :=
⟨λ x, option.rec (sum.inl ()) sum.inr x,
 λ x, sum.rec (λ _, option.none) option.some x,
 λ x, by induction x; repeat { simp },
 λ x, begin induction x, { induction x, simp }, simp end⟩

def cf (n : ℕ) : ℕ := ite (n < 2) 1 0

def cf_lemma {n} : cf (n + 2) = 0 :=
begin
  have h : ¬ n + 2 < 2 := nat.not_lt_zero n ∘ nat.lt_of_succ_lt_succ ∘ nat.lt_of_succ_lt_succ,
  simp [cf, if_neg h]
end

def ogf_iso {α} : option α ≃ ogf cf α :=
begin
  apply (def_iso ⋆ _),
  apply (_ ⋆ ax₁.inv),
  apply (_ ⋆ iso.add_left (iso.unit_mul_left ⋆ iso.mul fin.unit_iso.inv fseq.unit_iso.inv)),
  apply iso.add_right,
  apply (_ ⋆ ax₁.inv),
  apply (_ ⋆ iso.add_left (iso.unit_mul_left ⋆ iso.mul fin.unit_iso.inv fseq.id_iso.inv)),
  apply (iso.empty_add_right ⋆ _),
  apply iso.add_right,
  simp [cf_lemma],
  apply (_ ⋆ iso.sigma_subst (λ n, iso.empty_mul_left ⋆ (@iso.mul_left _ _ (fseq (n + 2) α)) fin.empty_iso.inv)),
  apply iso.sigma_empty.inv
end
end option

namespace nat
-- ℕ = 1 + ℕ
def def_iso : ℕ ≃ unit ⊕ ℕ :=
⟨λ x, nat.rec (sum.inl ()) (λ y ih, sum.inr y) x,
 λ x, sum.rec (λ y, 0) (λ y, y+1) x,
 λ x, begin induction x with x ih, repeat { refl } end,
 λ x, begin induction x, { induction x, refl }, refl end⟩

-- ℕ = Σ n:ℕ, 1
def ogf_iso : ℕ ≃ ogf (K 1) unit :=
iso.sigma_unit⁻¹ ⋆ iso.sigma_subst (λ n, iso.unit_mul_left ⋆ (iso.mul fin.unit_iso fseq.unit_iso₂)⁻¹)
end nat

-- Geometric power series
-- geom(x) = Σ n:ℕ, xⁿ
def geom (α) := Σ n, fseq n α

namespace geom
-- geom(x) = 1 + x geom(x)
def lin_iso {α} : geom α ≃ unit ⊕ α × (geom α) :=
ax₁ ⋆ iso.add fseq.unit_iso (iso.sigma_subst (λ n, fseq.cons_iso⁻¹) ⋆ ax₂)

-- geom(x) = Σ n:ℕ, xⁿ
def ogf_iso {α} : geom α ≃ ogf (K 1) α :=
iso.sigma_subst (λ n, iso.unit_mul_left ⋆ iso.mul_left fin.unit_iso⁻¹)
end geom

inductive vec (α : Type) : ℕ → Type
| nil : vec 0
| cons {n} : α → vec n → vec (n+1)

namespace vec
def def_iso₁ {α} : vec α 0 ≃ unit :=
⟨λ x, (),
 λ x, vec.nil α,
 λ x, match x with
 | vec.nil α := rfl
 end,
 λ x, begin induction x, refl end⟩

def def_iso₂ {n α} : vec α (n+1) ≃ α × (vec α n) :=
⟨λ x, match x with
 | vec.cons h t := (h, t)
 end,
 λ x, vec.cons x.1 x.2,
 λ x, match x with
 | vec.cons h t := rfl
 end,
 λ x, by simp [def_iso₂._match_1]⟩

def fseq_iso {n α} : vec α n ≃ fseq n α :=
begin
  induction n with n ih,
  { exact (def_iso₁ ⋆ fseq.unit_iso.inv) },
  apply (def_iso₂ ⋆ _),
  apply (_ ⋆ fseq.cons_iso),
  apply iso.mul_right,
  apply ih
end

def geom_iso {α} : (Σ n, vec α n) ≃ geom α :=
iso.sigma_subst (λ n, fseq_iso)

def ogf_iso {n α} : vec α n ≃ ogf (delta n) α :=
fseq_iso ⋆ fseq.ogf_iso

def ogf_iso₁ {α} : (Σ n, vec α n) ≃ ogf (K 1) α :=
geom_iso ⋆ geom.ogf_iso
end vec

namespace list
-- list(x) = 1 + x list(x) = 1/(1-x)
def def_iso {α} : list α ≃ unit ⊕ α × (list α) :=
⟨λ x, list.rec (sum.inl ()) (λ h t ih, sum.inr (h, t)) x,
 λ x, sum.rec (λ y, []) (λ y, y.1 :: y.2) x,
 λ x, by induction x; repeat { simp },
 λ x, by induction x; { induction x, refl }; { simp }⟩

def vec_iso {α} : list α ≃ Σ n, vec α n :=
⟨λ x, list.rec ⟨0, vec.nil α⟩ (λ h t ih, ⟨ih.1+1, vec.cons h ih.2⟩) x,
 λ x, vec.rec [] (λ n h t ih, h :: ih) x.2,
 λ x, begin induction x with h t ih, { refl }, simp [ih] end,
 λ x, begin induction x with x₁ x₂, induction x₂ with n h t ih, { refl }, { simp [ih], rw ih } end⟩

def geom_iso {α} : list α ≃ geom α :=
vec_iso ⋆ vec.geom_iso

-- list(x) = Σ n:ℕ, xⁿ
def ogf_iso {α} : list α ≃ ogf (K 1) α :=
geom_iso ⋆ geom.ogf_iso

-- list(1) = ℕ
def nat_iso : list unit ≃ ℕ :=
ogf_iso ⋆ nat.ogf_iso⁻¹
end list

namespace fins
-- 0⁰ = 1
def unit_iso : fin 0 → fin 0 ≃ unit :=
⟨λ x, (),
 λ x, fin.elim0,
 λ x, funext (λ y, fin.elim0 y),
 λ x, by induction x; refl⟩

-- 0ⁿ⁺¹ = 0
def empty_iso {n} : fin (n + 1) → fin 0 ≃ empty :=
⟨λ x, fin.elim0 (x 0),
 λ x, empty.rec _ x,
 λ x, funext (λ y, fin.elim0 (x y)),
 λ x, empty.rec _ x⟩

-- Σ k, nᵏ = 1/(1-n)
def list_iso {n} : (Σ k, fin k → fin n) ≃ list (fin n) :=
list.geom_iso⁻¹

-- Σ k, nᵏ = ogf (λ k, n^k) 1
def ogf_iso {n} : (Σ k, fin k → fin n) ≃ ogf (λ k, n^k) unit :=
iso.sigma_subst (λ k, iso.unit_mul_right ⋆ iso.mul fin.pow_iso fseq.unit_iso₂⁻¹)
end fins

-- list(0) = 1
def list_unit_iso : list empty ≃ unit :=
iso.map fin.empty_iso⁻¹ ⋆ list.geom_iso ⋆ ax₁ ⋆
  iso.add fins.unit_iso (iso.sigma_subst (λ n, fins.empty_iso) ⋆ iso.sigma_empty) ⋆ iso.empty_add_right⁻¹

-- Balanced Trees[4,5,6]
-- [4] https://github.com/skaslev/papers/blob/master/iterating.pdf
-- [5] https://github.com/skaslev/papers/blob/master/balanced.pdf
-- [6] https://github.com/skaslev/papers/blob/master/balanced-comb.pdf

-- f(x) = x + f(g(x)) ↔ f(x) = Σ n:ℕ, gⁿ(x)
inductive F (g : Type → Type) : Type → Type 1
| F₀ {α} : α → F α
| F₁ {α} : F (g α) → F α

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
def f_iso {g : Type → Type} {α} : S g α ≃ F g α :=
⟨code, deco, deco_code, code_deco⟩
end S

-- g(x) = x + x g(x) ↔ g(x) = x/(1-x) ↔ gⁿ(x) = x/(1-nx)
inductive G (α : Type) : Type
| G₀ : α → G
| G₁ : α → G → G

namespace G
-- g(x) = x + x g(x)
def def_iso {α} : G α ≃ α ⊕ α × (G α) :=
⟨λ x, G.rec sum.inl (λ h t ih, sum.inr (h, t)) x,
 λ x, sum.rec G.G₀ (λ y, G.G₁ y.1 y.2) x,
 λ x, by induction x; repeat { refl },
 λ x, by induction x; repeat { simp }⟩

-- g(x) = x (1 + g(x))
def mul_iso {α} : G α ≃ α × (unit ⊕ G α) :=
def_iso ⋆ iso.distr_unit_left

-- g(x) = x/(1-x)
def list_iso {α} : G α ≃ α × (list α) :=
⟨λ x, G.rec (λ h, (h, [])) (λ h t ih, (ih.1, h :: ih.2)) x,
 λ x, list.rec (G.G₀ x.1) (λ h t ih, G.G₁ h ih) x.2,
 λ x, begin induction x with h h t ih, { refl }, { simp [ih] } end,
 λ x, begin induction x with x₁ x₂, induction x₂ with h t ih, { refl }, simp [ih] end⟩

-- 1 + g(x) = 1/(1-x)
def list_iso₁ {α} : unit ⊕ G α ≃ list α :=
iso.add_right list_iso ⋆ list.def_iso⁻¹

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

-- g(x) = Σ k:ℕ, xᵏ⁺¹
def ogf_iso {α} : G α ≃ ogf cf α :=
eq.mp (by rw cf_lemma) (list_iso ⋆ iso.mul id.ogf_iso list.ogf_iso ⋆ ogf.mul_iso)
end G

namespace Gⁿ
-- gⁿ(x) = x + n x gⁿ(x)
def lin_iso {n α} : iter G n α ≃ α ⊕ (fin n × α) × (iter G n α) :=
begin
  induction n with n ih generalizing α,
  { exact (iso.empty_add_right ⋆ iso.add_right (iso.empty_mul_left ⋆ iso.mul_left (iso.empty_mul_left ⋆ iso.mul_left fin.empty_iso.inv))) },
  apply (ih ⋆ _),
  apply (iso.add_right (iso.mul_left iso.mul_comm ⋆ iso.mul_assoc.inv) ⋆ _),
  apply (iso.distr_unit_left ⋆ _),
  apply (iso.mul_left G.mul_iso ⋆ iso.mul_assoc.inv ⋆ _),
  apply (_ ⋆ iso.add_right (iso.mul_assoc ⋆ iso.mul_left iso.mul_comm)),
  apply (_ ⋆ iso.distr_unit_left.inv),
  apply iso.mul_right,
  apply (iso.distr_unit_right.inv ⋆ iso.add_assoc.inv ⋆ _),
  apply iso.add_right,
  apply (_ ⋆ iso.mul_left fin.add_unit_iso),
  apply (_ ⋆ iso.add_comm ⋆ iso.distr_unit_right),
  apply iso.add_right,
  apply (iso.distr_unit_left.inv ⋆ _),
  apply (iso.add_right (iso.mul_assoc ⋆ iso.mul_left iso.mul_comm.inv) ⋆ _),
  apply ih.inv
end

-- gⁿ(x) = x/(1-nx)
def list_iso {n α} : iter G n α ≃ α × list (fin n × α) :=
sorry

-- n gⁿ(x) = g(nx)
def gn_iso {n α} : fin n × iter G n α ≃ G (fin n × α) :=
iso.mul_right list_iso ⋆ iso.mul_assoc ⋆ G.list_iso⁻¹

-- m gⁿᵐ(x) = gⁿ(mx)
def gnm_iso {n m α} : fin m × iter G (n*m) α ≃ iter G n (fin m × α) :=
begin
  apply (_ ⋆ list_iso.inv),
  apply (iso.mul_right list_iso ⋆ _),
  apply (iso.mul_assoc ⋆ _),
  apply iso.mul_right,
  exact iso.map (iso.mul_left fin.mul_iso.inv ⋆ iso.mul_assoc.inv)
end

-- n gⁿᵐ(x) = gᵐ(nx)
def gmn_iso {n m α} : fin n × iter G (n*m) α ≃ iter G m (fin n × α) :=
begin rw nat.mul_comm, exact gnm_iso end

-- gⁿ(1) = 1/(1-n)
def list_iso₁ {n} : iter G n unit ≃ list (fin n) :=
list_iso ⋆ iso.unit_mul_left⁻¹ ⋆ iso.map iso.unit_mul_right⁻¹

-- gⁿ(x) = Σ k:ℕ, nᵏ x^(k+1) = x (Σ k:ℕ, nᵏxᵏ) = x/(1-nx)
-- ⇒ gⁿ(1) = Σ k:ℕ, fin k → fin n
-- ⇒ f(1) = Σ n:ℕ, gⁿ(1) = Σ n:ℕ, Σ k:ℕ, fin k → fin n
def fins_iso {n} : iter G n unit ≃ Σ k, fin k → fin n :=
list_iso₁ ⋆ fins.list_iso⁻¹

def cf (n k : ℕ) : ℕ := dite (k = 0) (λ _, 0) (λ _, n^(k-1))

def cf_lemma₁ (n : ℕ) : cf n 0 = 0 :=
by simp [cf]

def cf_lemma₂ (n k : ℕ) : cf n (k+1) = n^k :=
by simp [cf, dif_neg (nat.succ_ne_zero k)]

-- gⁿ(x) = Σ k:ℕ, nᵏ xᵏ⁺¹
def ogf_iso {n α} : iter G n α ≃ ogf (cf n) α :=
begin
  apply (list_iso ⋆ iso.mul_right list.geom_iso ⋆ _),
  apply (_ ⋆ ax₁.inv),
  rw cf_lemma₁,
  apply (_ ⋆ iso.empty_add_right ⋆ iso.add_comm ⋆ iso.add_left (iso.empty_mul_left ⋆ iso.mul_left fin.empty_iso.inv)),
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
end Gⁿ

namespace SG
def fins_iso : S G unit ≃ Σ n k, fin k → fin n :=
iso.sigma_subst (λ n, Gⁿ.fins_iso)

def list_iso {α} : S G α ≃ Σ n, α × list (fin n × α) :=
iso.sigma_subst (λ n, Gⁿ.list_iso)

def list_iso₁ : S G unit ≃ Σ n, list (fin n) :=
fins_iso ⋆ iso.sigma_subst (λ n, fins.list_iso)
end SG

namespace FG
def fins_iso : F G unit ≃ Σ n k, fin k → fin n :=
S.f_iso⁻¹ ⋆ SG.fins_iso

def list_iso {α} : F G α ≃ Σ n, α × list (fin n × α) :=
S.f_iso⁻¹ ⋆ SG.list_iso

def list_iso₁ : F G unit ≃ Σ n, list (fin n) :=
S.f_iso⁻¹ ⋆ SG.list_iso₁
end FG

-- From Generatingfunctionology[7] pg. 18
-- B₀(x) = 1, ∀ k>0:
-- Bₖ(x) = x Bₖ₋₁(x) + k x Bₖ(x)
-- ⇒ Bₖ x = x/(1-kx) Bₖ₋₁(x)
-- [7] https://www.math.upenn.edu/~wilf/gfologyLinked2.pdf
inductive B (α : Type) : ℕ → Type
| B₀ : B 0
| B₁ {k} : α → (B k) → B (k+1)
| B₂ {k} : α → fin (k+1) → B (k+1) → B (k+1)

def ogf_skel (f : ℕ → ℕ) (α) := Σ β : Type → Type, β α ≃ ogf f α
def ogf_fixed (f : ℕ → ℕ) := Σ α, α ≃ ogf f α

def icyc := Σ' p : ℕ → ℕ, ∀ i, p i = p 0 + i
def icyclic (α) (a b : iseq α) := ∃ p : icyc, (a ∘ p.1) = b
def isec (α) := quot (icyclic α)
-- igf c x = Σ n : ℕ, cₙ x^ℕ / ℕ
def igf (c : ℕ → ℕ) (α) :=
Σ n : ℕ, fin (c n) × isec α

namespace linear
variable linear : Π {α β γ : Type}, (γ ≃ α ⊕ β × γ) → (γ ≃ α × list β)

def wat : unit ≃ empty :=
linear (iso.unit_mul_left ⋆ iso.empty_add_left) ⋆ iso.empty_mul_left⁻¹
end linear
