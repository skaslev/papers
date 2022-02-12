import function
import type

structure {u v} iso (A : Sort u) (B : Sort v) :=
(f : A → B)
(g : B → A)
(gf : Π x, g (f x) = x)
(fg : Π x, f (g x) = x)

notation a ` ≃ ` b := iso a b

instance {A B} : has_coe_to_fun (A ≃ B) :=
{ F := λ i, A → B, coe := λ i, i.1 }

-- Types        Algebra
-- A            a
-- A ⊕ B        a + b
-- A × B        ab
-- A → B        bᵃ
-- Σ n, f n     Σ n, fₙ
-- Π n, f n     Π n, fₙ
-- A ≃ B        a = b

def is_isomorphic (A B) : Prop := nonempty (A ≃ B)
def skeleton : Type* := quot is_isomorphic

namespace iso
def id_iso {A} : A ≃ A :=
⟨id, id, by simp [id], by simp [id]⟩

def inv {A B} (i : A ≃ B) : B ≃ A :=
⟨i.g, i.f, i.fg, i.gf⟩

def comp {A B C} (i : A ≃ B) (j : B ≃ C) : A ≃ C :=
⟨j.f ∘ i.f, i.g ∘ j.g, by simp [j.gf, i.gf], by simp [i.fg, j.fg]⟩

notation a ⁻¹  := inv a
notation a ` ⋆ ` b := comp a b

def map {f} [functor f] [is_lawful_functor f] {A B} (i : A ≃ B) : f A ≃ f B :=
⟨functor.map i.f,
 functor.map i.g,
 λ x, by rw ←is_lawful_functor.comp_map; simp [i.gf]; rw [←id_def, is_lawful_functor.id_map],
 λ x, by rw ←is_lawful_functor.comp_map; simp [i.fg]; rw [←id_def, is_lawful_functor.id_map]⟩

def add {A B C D} (i : A ≃ B) (j : C ≃ D) : A ⊕ C ≃ B ⊕ D :=
⟨function.add i.f j.f,
 function.add i.g j.g,
 λ x, sum.rec (by simp [function.add, i.gf]) (by simp [function.add, j.gf]) x,
 λ x, sum.rec (by simp [function.add, i.fg]) (by simp [function.add, j.fg]) x⟩

def mul {A B C D} (i : A ≃ B) (j : C ≃ D) : A × C ≃ B × D :=
⟨function.mul i.f j.f,
 function.mul i.g j.g,
 by simp [function.mul, i.gf, j.gf],
 by simp [function.mul, i.fg, j.fg]⟩

def dimap {A B C D} (i : A ≃ B) (j : C ≃ D) : B → C ≃ A → D :=
⟨function.dimap i.f j.f,
 function.dimap i.g j.g,
 λ x, funext (by simp [function.dimap, i.fg, j.gf]),
 λ x, funext (by simp [function.dimap, i.gf, j.fg])⟩

def add_left {A B C} (i : A ≃ B) : A ⊕ C ≃ B ⊕ C :=
add i id_iso

def add_right {A C D} (i : C ≃ D) : A ⊕ C ≃ A ⊕ D :=
add id_iso i

def mul_left {A B C} (i : A ≃ B) : A × C ≃ B × C :=
mul i id_iso

def mul_right {A C D} (i : C ≃ D) : A × C ≃ A × D :=
mul id_iso i

def func {A B C D} (i : A ≃ B) (j : C ≃ D) : A → C ≃ B → D :=
dimap i⁻¹ j

def func_right {A B C} (i : B ≃ C) : A → B ≃ A → C :=
func id_iso i

def func_left {A B C} (i : A ≃ B) : A → C ≃ B → C :=
func i id_iso

-- (cᵇ)ᵃ = cᵃᵇ
def curry {A B C : Type} : A → B → C ≃ (A × B) → C :=
⟨λ f x, f x.1 x.2, λ f x y, f (x, y), by simp, by simp⟩

-- cᵃ cᵇ = cᵃ⁺ᵇ
def mul_func₁ {A B C : Type} : (A → C) × (B → C) ≃ (A ⊕ B) → C :=
⟨λ x y, sum.rec x.1 x.2 y,
 λ x, (x ∘ sum.inl, x ∘ sum.inr),
 λ x, by simp,
 λ x, by funext y; induction y; repeat { simp }⟩

-- bᵃ cᵃ = (bc)ᵃ
def mul_func₂ {A B C : Type} : (A → B) × (A → C) ≃ A → B × C :=
⟨λ x y, (x.1 y, x.2 y),
 λ x, (λ y, (x y).1, λ y, (x y).2),
 λ x, by induction x with x₁ x₂; congr,
 λ x, funext (λ y, by simp)⟩

 def pi_one {A} : (Π a:A, 1) ≃ 1 :=
⟨λ x, unit.star,
 λ x y, x,
 λ x, funext (λ a, isprop_one _ _),
 λ x, isprop_one _ _⟩

 def pi_curry {A B} {C : A → B → Type*} : (Π a, Π b, C a b) ≃ Π (i : A × B), C i.1 i.2 :=
⟨λ f x, f x.1 x.2,
 λ f x y, f ⟨x, y⟩,
 λ x, funext (λ y, rfl),
 λ x, funext (λ ⟨a,b⟩, rfl)⟩

 def pi_sigma_curry {A B} {C : A → Type*} : (Π a, C a → B) ≃ Π (i : Σ a, C a), B :=
⟨λ f x, f x.1 x.2,
 λ f x y, f ⟨x, y⟩,
 λ x, funext (λ y, rfl),
 λ x, funext (λ ⟨a,b⟩, rfl)⟩

def sigma_subst {A : Type*} {B C : A → Type*} (i : Π a:A, B a ≃ C a) : (Σ a:A, B a) ≃ Σ a:A, C a :=
⟨λ x, ⟨x.1, (i x.1).f x.2⟩,
 λ x, ⟨x.1, (i x.1).g x.2⟩,
 λ x, begin induction x with x₁ x₂, simp [(i x₁).gf] end,
 λ x, begin induction x with x₁ x₂, simp [(i x₁).fg] end⟩

def sigma_add {A} {B C : A → Type} : ((Σ a:A, B a) ⊕ (Σ a:A, C a)) ≃ Σ a:A, B a ⊕ C a :=
⟨λ x, sum.rec (λ y, ⟨y.1, sum.inl y.2⟩) (λ y, ⟨y.1, sum.inr y.2⟩) x,
 λ x, sum.rec (λ y, sum.inl ⟨x.1, y⟩) (λ y, sum.inr ⟨x.1, y⟩) x.2,
 λ x, by induction x; repeat { dsimp, rw sigma.mk.eta },
 λ x, by induction x with x₁ x₂; induction x₂; repeat { refl }⟩

def sigma_distr {A B} {C : B → Type} : (A × Σ b:B, C b) ≃ Σ b:B, A × C b :=
⟨λ x, ⟨x.2.1, (x.1, x.2.2)⟩,
 λ x, (x.2.1, ⟨x.1, x.2.2⟩),
 λ x, by simp,
 λ x, by induction x with x₁ x₂; simp⟩

def sigma_pull {A} {B C : A → Type*} : (Σ a, B a × C a) ≃ Σ (i : Σ a, B a), C i.1 :=
⟨λ ⟨x, ⟨y, z⟩⟩, ⟨⟨x, y⟩, z⟩,
 λ ⟨⟨x, y⟩, z⟩, ⟨x, ⟨y, z⟩⟩,
 λ ⟨x, ⟨y, z⟩⟩, rfl,
 λ ⟨⟨x, y⟩, z⟩, rfl⟩

def sigma_swap {C : ℕ → ℕ → Type}: (Σ n k, C n k) ≃ Σ k n, C n k :=
⟨λ x, ⟨x.2.1, ⟨x.1, x.2.2⟩⟩,
 λ x, ⟨x.2.1, ⟨x.1, x.2.2⟩⟩,
 λ x, by simp,
 λ x, by simp⟩

def sigma_zero {A} : (Σ a:A, 0) ≃ 0 :=
⟨λ x, x.2, pempty.rec _,
 λ x, pempty.rec _ x.2, pempty.rec _⟩

def sigma_one {A} : (Σ a:A, 1) ≃ A :=
⟨λ x, x.1,
 λ x, ⟨x, ()⟩,
 λ x, by induction x with x₁ x₂; induction x₂; refl,
 λ x, by simp⟩

def sigma_subst_zero {A} {B : A → Type} (i : Π a, B a ≃ 0): (Σ a:A, B a) ≃ 0 :=
sigma_subst i ⋆ sigma_zero

def add_comm {A B} : A ⊕ B ≃ B ⊕ A :=
⟨λ x, sum.rec sum.inr sum.inl x,
 λ x, sum.rec sum.inr sum.inl x,
 λ x, by induction x; simp,
 λ x, by induction x; simp⟩

def mul_comm {A B} : A × B ≃ B × A :=
⟨λ x, (x.2, x.1), λ x, (x.2, x.1), by simp, by simp⟩

def add_assoc {A B C} : A ⊕ (B ⊕ C) ≃ (A ⊕ B) ⊕ C :=
⟨λ x, sum.rec (sum.inl ∘ sum.inl) (λ y, sum.rec (sum.inl ∘ sum.inr) sum.inr y) x,
 λ x, sum.rec (λ y, sum.rec sum.inl (sum.inr ∘ sum.inl) y) (sum.inr ∘ sum.inr) x,
 λ x, by repeat { induction x, repeat { refl } },
 λ x, by repeat { induction x, repeat { refl } }⟩

def mul_assoc {A B C} : A × (B × C) ≃ (A × B) × C :=
⟨λ x, ((x.1, x.2.1), x.2.2),
 λ x, (x.1.1, (x.1.2, x.2)),
 λ x, by simp,
 λ x, by simp⟩

def distr_right {A B C} : (A ⊕ B) × C ≃ A × C ⊕ B × C :=
⟨λ x, sum.rec (λ y, sum.inl (y, x.2)) (λ y, sum.inr (y, x.2)) x.1,
 λ x, sum.rec (λ y, (sum.inl y.1, y.2)) (λ y, (sum.inr y.1, y.2)) x,
 λ x, by induction x with x₁ x₂; induction x₁; repeat { simp },
 λ x, by induction x; repeat { simp }⟩

def distr_left {A B C} : A × (B ⊕ C) ≃ A × B ⊕ A × C :=
mul_comm ⋆ distr_right ⋆ add mul_comm mul_comm

def add_zero_right {A} : A ≃ A ⊕ 0 :=
⟨sum.inl, λ x, sum.rec id (pempty.rec _) x,
 λ x, rfl, λ x, sum.rec (λ y, rfl) (pempty.rec _) x⟩

def add_zero_left {A} : A ≃ 0 ⊕ A :=
add_zero_right ⋆ add_comm

def mul_zero_right {A} : 0 ≃ A × 0 :=
⟨λ x, pempty.rec _ x, λ x, pempty.rec _ x.2,
 λ x, pempty.rec _ x, λ x, pempty.rec _ x.2⟩

def mul_zero_left {A} : 0 ≃ 0 × A :=
mul_zero_right ⋆ mul_comm

def mul_one_right {A} : A ≃ A × 1 :=
⟨λ x, (x, ()),
 λ x, x.1,
 λ x, by simp,
 λ x, by induction x with x₁ x₂; congr⟩

def mul_one_left {A} : A ≃ 1 × A :=
mul_one_right ⋆ mul_comm

def distr_one_left {A B} : A ⊕ A × B ≃ A × (1 ⊕ B) :=
add_left mul_one_right ⋆ distr_left⁻¹

def distr_one_right {A B} : A ⊕ B × A ≃ (1 ⊕ B) × A :=
add_right mul_comm ⋆ distr_one_left ⋆ mul_comm

def add_zero_right_subst {A B C} (i : A ≃ B) (j : C ≃ 0) : A ≃ B ⊕ C :=
i ⋆ add_zero_right ⋆ add_right j⁻¹

def iter_iso {f : Type → Type} [functor f] [is_lawful_functor f] {A} (i : A ≃ f A) (n) : A ≃ iter f n A :=
begin
  induction n with n ih generalizing A,
  { exact iso.id_iso },
  { exact (i ⋆ ih (iso.map i)) }
end

open combinator

def const_iso {A B : Type} : A ≃ (const A B) :=
iso.id_iso
end iso

def lt_one {n : ℕ} (g : n < 1) : n = 0 :=
begin
  induction n with n ih,
  { refl },
  { exact false.elim (nat.not_lt_zero n (nat.lt_of_succ_lt_succ g)) }
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
     { rw nat.sub_add_cancel,
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

def ax₂ {f : ℕ → Type} {A} : (Σ n:ℕ, A × f n) ≃ A × Σ n:ℕ, f n :=
iso.sigma_distr⁻¹
end generic_summation

namespace iso
universes u v w
variables {f : Type u → Type v} {g : Type u → Type w} (i : Π {A}, iso (f A) (g A))

def imap [functor f] {A B : Type u} (s : A → B) (x : g A) : g B :=
i.f $ s <$> i.g x

def ipure [applicative f] {A : Type u} (x : A) : g A :=
i.f $ pure x

def iseq [applicative f] {A B : Type u} (s : g (A → B)) (x : g A) : g B :=
i.f $ i.g s <*> i.g x

def ibind [monad f] {A B : Type u} (x : g A) (s : A → g B) : g B :=
i.f $ i.g x >>= i.g ∘ s

-- @[priority std.priority.default-1]
-- instance functor [functor f] : functor g :=
-- { map := @imap f g @i _ }

-- @[priority std.priority.default-1]
-- instance is_lawful_functor [functor f] : is_lawful_functor g :=
-- { id_map :=
--   begin
--     intros,
--     simp [imap, is_lawful_functor.id_map, i.fg]
--   end,
--   comp_map :=
--   begin
--     intros,
--     simp [imap, i.gf],
--     rw is_lawful_functor.comp_map
--   end }

-- @[priority std.priority.default-1]
-- instance applicative [applicative f] : applicative g :=
-- { pure := @ipure f g @i _,
--   seq := @iseq f g @i _ }

-- @[priority std.priority.default-1]
-- instance is_lawful_applicative [is_lawful_applicative f] : is_lawful_applicative g :=
-- { pure_seq_eq_map := by intros; simp,
--   id_map :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_functor.id_map, i.fg]
--   end,
--   map_pure :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_applicative.map_pure]
--   end,
--   seq_pure :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_applicative.seq_pure]
--   end,
--   seq_assoc :=
--   begin
--     intros,
--     simp [ipure, iseq, i.gf],
--     simp [is_lawful_applicative.pure_seq_eq_map, is_lawful_applicative.seq_assoc]
--   end }

-- @[priority std.priority.default-1]
-- instance monad [monad f] : monad g :=
-- { pure := @ipure f g @i _,
--   bind := @ibind f g @i _ }

-- @[priority std.priority.default-1]
-- instance is_lawful_monad [is_lawful_monad f] : is_lawful_monad g :=
-- { id_map :=
--   begin
--     intros,
--     simp [ipure, ibind, i.gf],
--     rw monad.bind_pure_comp_eq_map,
--     simp [is_lawful_functor.id_map, i.fg]
--   end,
--   pure_bind :=
--   begin
--     intros,
--     simp [ipure, ibind, i.gf],
--     simp [is_lawful_monad.pure_bind, i.fg]
--   end,
--   bind_assoc :=
--   begin
--     intros,
--     simp [ibind, i.gf],
--     simp [is_lawful_monad.bind_assoc]
--   end }
end iso
